import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.TorusFibreMaximality
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Base change of fibrewise coordinate root data -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

variable {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')
  (I : Type u) [Finite I]

/-- The canonical coordinate identifications agree for successive base changes. -/
theorem baseChangeIso_comp_finite :
    (baseChange c).map (baseChangeIso b I).hom ≫ (baseChangeIso c I).hom =
      (baseChangeCompIso b c (splitTorus S I)).inv ≫
        (baseChangeIso (c ≫ b) I).hom := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv I T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_baseChangeIso_hom c I T, baseChangePointsEquiv,
    MulEquiv.trans_apply, GroupScheme.baseChangePointsEquiv_comp]
  erw [pointsEquiv_baseChangeIso_hom b I ((Over.map c).obj T)]
  rw [pointsEquiv_baseChangeIso_hom (c ≫ b) I T]
  simp only [baseChangePointsEquiv, MulEquiv.trans_apply]
  rw [GroupScheme.baseChangePointsEquiv_base_comp]
  erw [pointsEquiv_naturality]

/-- The inverse coordinate identifications agree for successive base changes. -/
theorem baseChangeIso_inv_comp :
    (baseChangeIso c I).inv ≫ (baseChange c).map (baseChangeIso b I).inv =
      (baseChangeIso (c ≫ b) I).inv ≫
        (baseChangeCompIso b c (splitTorus S I)).hom := by
  have h : (baseChange c).mapIso (baseChangeIso b I) ≪≫ baseChangeIso c I =
      (baseChangeCompIso b c (splitTorus S I)).symm ≪≫ baseChangeIso (c ≫ b) I :=
    Iso.ext (baseChangeIso_comp_finite b c I)
  exact congrArg Iso.inv h

/-- Canonical coordinate torus maps agree in a composite and successive pullback. -/
theorem baseChangeTorusHom_comp (G : GroupScheme S) (i : splitTorus S I ⟶ G) :
    (baseChangeIso c I).inv ≫
        (baseChange c).map ((baseChangeIso b I).inv ≫ (baseChange b).map i) =
      ((baseChangeIso (c ≫ b) I).inv ≫ (baseChange (c ≫ b)).map i) ≫
        (baseChangeCompIso b c G).hom := by
  rw [Functor.map_comp, ← Category.assoc, baseChangeIso_inv_comp]
  have hn := ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i
  change (baseChange (c ≫ b)).map i ≫ (baseChangeCompIso b c G).hom =
    (baseChangeCompIso b c (splitTorus S I)).hom ≫
      (baseChange c).map ((baseChange b).map i) at hn
  simpa only [Category.assoc] using
    congrArg (fun f => (baseChangeIso (c ≫ b) I).inv ≫ f) hn.symm

end splitTorus

section Maximality

variable {S S' : Scheme.{u}} {T T' : CommGroupScheme S} {G : GroupScheme S}
  {i : T.toGrp ⟶ G}

end Maximality

section AmbientTransport

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

private theorem rootDatum_compIso {J : Type v} {i : T.toGrp ⟶ G}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (e : G ≅ H) : IsRootDatumOf (i ≫ e.hom) P := by
  refine ⟨hP.1, ?_, fun α => ?_⟩
  · have hs : i ≫ e.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ e.hom) :=
      (Category.id_comp _).symm
    have hchar : ⇑(characterLattice.congr (Iso.refl T)) = id := by
      funext a
      exact Category.id_comp a
    rw [hP.2.1, ← roots_image_of_transport (Iso.refl T) e hs, hchar, Set.image_id]
  · obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
    refine ⟨n ≫ e.hom.hom.hom, σ, ?_, hσ⟩
    unfold IsNormalizingPoint at hn ⊢
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hn, Category.assoc]

end AmbientTransport

section AffineBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance fibrewisePullbackAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

/-- The canonical coordinate torus after arbitrary scalar extension remains
maximal on every residue-field fibre. -/
theorem splitTorus.isFibrewiseMaximalTorus_baseChangeHom [Smooth G.X.hom]
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := A) G I i) :=
  IsFibrewiseMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange (algebraBaseMap R A)).obj
      (splitTorus.commGroupScheme _ I))
    (T' := splitTorus.commGroupScheme _ I)
    (hi.baseChange (algebraBaseMap R A))
    (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm

/-- Package the affine pullback instance with the map being transported. -/
private def coordinateRootDatumAt {J : Type v}
    (P : RootDatum J (I → ℤ) (I → ℤ)) (k : Type u) [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) : Prop :=
  letI : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  IsRootDatumOf (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i)
    (CoordinateRootDatum.fieldRealization k P)

/-- The same complete coordinate datum remains a fibrewise root datum after
arbitrary extension of the coefficient ring. -/
def FibrewiseRootDatumBaseChangeStatement : Prop :=
  ∀ {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ)),
    IsFibrewiseRootDatumOf I G i P →
      IsFibrewiseRootDatumOf I ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
        (splitTorus.baseChangeHom (K := A) G I i) P

variable {I G i} {J : Type v} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Arbitrary scalar extension preserves the same full coordinate fibrewise
root datum, using the given field-algebra structure on each new fibre. -/
theorem IsFibrewiseRootDatumOf.baseChange_implicit
    (hP : IsFibrewiseRootDatumOf I G i P) :
    IsFibrewiseRootDatumOf I ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
      (splitTorus.baseChangeHom (K := A) G I i) P := by
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro k _ _
  let : Algebra R k := ((algebraMap A k).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq' rfl
  have ht : algebraBaseMap A k ≫ algebraBaseMap R A = algebraBaseMap R k := by
    unfold algebraBaseMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R A k]
  let : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap A k ≫ algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom
      (algebraBaseMap A k ≫ algebraBaseMap R A)))
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap A k)).obj
      ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd
      ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom (algebraBaseMap A k)))
  have hr : IsRootDatumOf
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      ((splitTorus.baseChangeIso (algebraBaseMap A k ≫ algebraBaseMap R A) I).inv ≫
        (GroupScheme.baseChange (algebraBaseMap A k ≫ algebraBaseMap R A)).map i)
      (CoordinateRootDatum.fieldRealization k P) := by
    change coordinateRootDatumAt I G i P k
      (algebraBaseMap A k ≫ algebraBaseMap R A)
    rw [ht]
    exact hP.field k
  change IsRootDatumOf
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    ((splitTorus.baseChangeIso (algebraBaseMap A k) I).inv ≫
      (GroupScheme.baseChange (algebraBaseMap A k)).map
        ((splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R A)).map i))
    (CoordinateRootDatum.fieldRealization k P)
  rw [splitTorus.baseChangeTorusHom_comp]
  exact rootDatum_compIso (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    hr (baseChangeCompIso (algebraBaseMap R A) (algebraBaseMap A k) G)

/-- Full coordinate root data are stable under arbitrary scalar extension. -/
theorem fibrewiseRootDatumBaseChange :
    FibrewiseRootDatumBaseChangeStatement (A := A) I G i :=
  fun _ hP => hP.baseChange_implicit

end AffineBaseChange

end Langlands.GroupScheme
