import Langlands.GroupScheme.IntegralModel.StrictHenselianModelPinning
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum

/-! # Transport of actual split data through pullback comparisons -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

variable {S S' S'' : Scheme.{u}} (a : S' ⟶ S) (b : S'' ⟶ S')
  (I : Type u) [Fintype I]

/-- The canonical split-torus comparisons respect composition of pullbacks. -/
theorem baseChangeIso_comp :
    (baseChange b).map (baseChangeIso a I).hom ≫ (baseChangeIso b I).hom =
      (baseChangeCompIso a b (splitTorus S I)).inv ≫
        (baseChangeIso (b ≫ a) I).hom := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv I T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_baseChangeIso_hom, pointsEquiv_baseChangeIso_hom]
  change pointsEquiv I ((Over.map b).obj T)
      (Langlands.GroupScheme.baseChangePointsEquiv b _ T
        (x ≫ ((baseChange b).map (baseChangeIso a I).hom).hom.hom)) =
    pointsEquiv I ((Over.map (b ≫ a)).obj T)
      (Langlands.GroupScheme.baseChangePointsEquiv (b ≫ a) _ T
        (x ≫ (baseChangeCompIso a b (splitTorus S I)).inv.hom.hom))
  rw [Langlands.GroupScheme.baseChangePointsEquiv_comp,
    pointsEquiv_baseChangeIso_hom]
  change pointsEquiv I ((Over.map a).obj ((Over.map b).obj T))
      (Langlands.GroupScheme.baseChangePointsEquiv a _ ((Over.map b).obj T)
        (Langlands.GroupScheme.baseChangePointsEquiv b _ T x)) = _
  rw [baseChangePointsEquiv_base_comp, pointsEquiv_naturality]
  simp [unitsRestrict]
  rfl

variable (G : GroupScheme S) (i : splitTorus S I ⟶ G)

/-- Applying canonical coordinate pullback twice agrees with applying it
along the composite, through the ambient pullback comparison. -/
theorem baseChangeHom_comp :
    (baseChangeIso b I).inv ≫
        (baseChange b).map ((baseChangeIso a I).inv ≫ (baseChange a).map i) ≫
        (baseChangeCompIso a b G).inv =
      (baseChangeIso (b ≫ a) I).inv ≫ (baseChange (b ≫ a)).map i := by
  have ht := baseChangeIso_comp a b I
  have ht' : (baseChangeIso b I).inv ≫
      (baseChange b).map (baseChangeIso a I).inv =
        (baseChangeIso (b ≫ a) I).inv ≫
          (baseChangeCompIso a b (splitTorus S I)).hom := by
    apply (cancel_mono ((baseChange b).map (baseChangeIso a I).hom ≫
      (baseChangeIso b I).hom)).mp
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
      ht, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
    Category.assoc, ← reassoc_of% (baseChangeCompIso_hom_naturality a b i),
    Iso.hom_inv_id, Category.comp_id]

end splitTorus

section AmbientIso

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (e : G ≅ H)

/-- An ambient isomorphism identifies the actual fixed-exponent weight
modules over an arbitrary ring. -/
def splitTorus.exponentWeightAmbientEquiv (m : I → ℤ) :
    splitTorus.exponentWeightSpace I G i m ≃ₗ[R]
      splitTorus.exponentWeightSpace I H (i ≫ e.hom) m := by
  rw [splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter,
    splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
  let E := weightSpaceTransportEquiv (Iso.refl (splitTorus.commGroupScheme _ I)) e
    (i := i) (j := i ≫ e.hom) (by change i ≫ e.hom = 𝟙 _ ≫ i ≫ e.hom; simp) (splitTorus.exponentCharacter _ I m)
  have hc : characterLattice.congr
      (Iso.refl (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m) =
        splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m := by
    change (𝟙 (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)) ≫
      splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m = _
    exact Category.id_comp _
  rw [hc] at E
  exact E

local instance {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

local instance {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj H).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R k)))

/-- Ambient group isomorphisms preserve the same full coordinate datum
on all supplied field fibres. -/
theorem IsFibrewiseRootDatumOf.comp_ambientIso {J : Type v}
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) :
    IsFibrewiseRootDatumOf I H (i ≫ e.hom) P := by
  refine ⟨hP.1, hP.2.1, fun k _ _ => ?_⟩
  simpa only [splitTorus.baseChangeHom, Functor.map_comp, Functor.mapIso_hom, Category.assoc] using
    (hP.field k).comp_iso ((baseChange (algebraBaseMap R k)).mapIso e)

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Ambient isomorphisms preserve residue-fibre maximality. -/
theorem IsFibrewiseMaximalTorus.comp_ambientIso
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) (i ≫ e.hom) := by
  intro p
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    (hi p).comp_iso ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField p)).mapIso e)

end AmbientIso

end Langlands.GroupScheme
