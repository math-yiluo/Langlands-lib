import Langlands.GroupScheme.Absolute.CentralizerProductTransporter
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Torus.HomFamilyRigidity

/-! # Rigidity of conjugation on the closure of a centralizer product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ConjugationInto

variable {S : Scheme.{u}} {H B G D : GroupScheme S} {U : Over S}
variable (s : H ⟶ G) (b : B ⟶ G) (g : U ⟶ G.X) (hg : Holds s b g)

/-- The unique point of `B` representing the inverse conjugate of the given point of `H`. -/
def conjugatePoint (V : Over S) (a : V ⟶ U) (t : V ⟶ H.X) : V ⟶ B.X :=
  (SubgroupFunctor.mem_range.mp (hg V a t)).choose

theorem conjugatePoint_comp (V : Over S) (a : V ⟶ U) (t : V ⟶ H.X) :
    conjugatePoint s b g hg V a t ≫ b.hom.hom =
      (a ≫ g)⁻¹ * (t ≫ s.hom.hom) * (a ≫ g) :=
  (SubgroupFunctor.mem_range.mp (hg V a t)).choose_spec

variable [Mono b.hom.hom]

theorem conjugatePoint_mul (V : Over S) (a : V ⟶ U) (t₁ t₂ : V ⟶ H.X) :
    conjugatePoint s b g hg V a (t₁ * t₂) =
      conjugatePoint s b g hg V a t₁ * conjugatePoint s b g hg V a t₂ := by
  apply (cancel_mono b.hom.hom).mp
  rw [MonObj.mul_comp, conjugatePoint_comp, conjugatePoint_comp, conjugatePoint_comp,
    MonObj.mul_comp]
  group

theorem conjugatePoint_naturality {V W : Over S} (f : W ⟶ V)
    (a : V ⟶ U) (t : V ⟶ H.X) :
    conjugatePoint s b g hg W (f ≫ a) (f ≫ t) =
      f ≫ conjugatePoint s b g hg V a t := by
  apply (cancel_mono b.hom.hom).mp
  simp only [Category.assoc, conjugatePoint_comp, MonObj.comp_mul, GrpObj.comp_inv]

theorem conjugatePoint_eq_of_parameter_one (ψ : H ⟶ B) (hψ : ψ ≫ b = s)
    {V : Over S} (a : V ⟶ U) (ha : a ≫ g = 1) (t : V ⟶ H.X) :
    conjugatePoint s b g hg V a t = t ≫ ψ.hom.hom := by
  apply (cancel_mono b.hom.hom).mp
  rw [conjugatePoint_comp, ha, inv_one, one_mul, mul_one, Category.assoc,
    ← Grp.comp_hom_hom, hψ]

/-- Any projection of this conjugation family to a split torus is independent of the
parameter, when the source is split and the parameter scheme is connected. -/
theorem projected_conjugatePoint_eq [ConnectedSpace U.left]
    (hH : IsSplitTorus H) (q : B ⟶ D) (hD : IsSplitTorus D)
    {V : Over S} (a a' : V ⟶ U) (t : V ⟶ H.X) :
    conjugatePoint s b g hg V a t ≫ q.hom.hom =
      conjugatePoint s b g hg V a' t ≫ q.hom.hom := by
  apply HomFamily.eq_of_connected hH hD
    (fun V a t => conjugatePoint s b g hg V a t ≫ q.hom.hom)
  · intro V a t₁ t₂
    rw [conjugatePoint_mul, MonObj.mul_comp]
  · intro V W f a t
    rw [conjugatePoint_naturality, Category.assoc]

/-- If one parameter maps to the identity, every projected inverse conjugate equals the
projection of the original homomorphism into `B`. -/
theorem projected_conjugatePoint_eq_of_parameter_one [ConnectedSpace U.left]
    (hH : IsSplitTorus H) (q : B ⟶ D) (hD : IsSplitTorus D)
    (ψ : H ⟶ B) (hψ : ψ ≫ b = s) {V : Over S}
    (a a₀ : V ⟶ U) (ha₀ : a₀ ≫ g = 1) (t : V ⟶ H.X) :
    conjugatePoint s b g hg V a t ≫ q.hom.hom = t ≫ (ψ ≫ q).hom.hom := by
  rw [projected_conjugatePoint_eq s b g hg hH q hD a a₀,
    conjugatePoint_eq_of_parameter_one s b g hg ψ hψ a₀ ha₀,
    Grp.comp_hom_hom, Category.assoc]

end ConjugationInto

namespace CentralizerProduct

variable {k : Type u} [Field k]
variable {M B G D : GroupScheme (Spec (CommRingCat.of k))}

/-- A morphism from a reduced source factors through the actual reduced product closure
whenever its underlying image lies in that closure. -/
theorem factors_closure_of_range_subset (j : M ⟶ G) (b : B ⟶ G)
    {V : Over (Spec (CommRingCat.of k))} [IsReduced V.left]
    (g : V ⟶ G.X)
    (hg : Set.range g.left ⊆ _root_.closure (Set.range (productHom j b).left)) :
    ∃ a : V ⟶ imageClosure j b, a ≫ closureInclusion j b = g := by
  have hker : (closureIdeal j b) ≤ g.left.ker :=
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).2 g.left hg
  have hi : (closureIdeal j b).subschemeι.ker ≤ g.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hker
  let al := IsClosedImmersion.lift (closureIdeal j b).subschemeι g.left hi
  have hal : al ≫ (closureIdeal j b).subschemeι = g.left :=
    IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk al ?_, Over.OverMorphism.ext hal⟩
  change al ≫ ((closureIdeal j b).subschemeι ≫ G.X.hom) = V.hom
  rw [← Category.assoc, hal, Over.w g]

/-- The identity section belongs to the actual reduced product closure. -/
theorem identity_factors (j : M ⟶ G) (b : B ⟶ G) :
    ∃ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ imageClosure j b,
      a ≫ closureInclusion j b = 1 := by
  let : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  apply factors_closure_of_range_subset j b
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
  have he : lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X)
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) ≫ productHom j b = 1 := by
    rw [lift_productHom, MonObj.one_comp, MonObj.one_comp, one_mul]
  rw [← he]
  rintro _ ⟨x, rfl⟩
  exact subset_closure ⟨_, rfl⟩

/-- Every projection of the closure's inverse-conjugation family to a split torus equals
the fixed projection of the cocharacter restricted to `B`. -/
theorem projected_conjugation_eq
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G) [Mono b.hom.hom]
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    (q : B ⟶ D) (hD : IsSplitTorus D)
    (V : Over (Spec (CommRingCat.of k))) (a : V ⟶ imageClosure j b)
    (t : V ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ConjugationInto.conjugatePoint χ b (closureInclusion j b)
      (closure_holds χ j hrep b hb hχ) V a t ≫ q.hom.hom =
        t ≫ (Dynamic.restrictCocharacter b χ hχ ≫ q).hom.hom := by
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : ConnectedSpace (imageClosure j b).left := imageClosure_connected j b
  obtain ⟨a₀, ha₀⟩ := identity_factors j b
  let c : V ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk V.hom (by simp)
  exact ConjugationInto.projected_conjugatePoint_eq_of_parameter_one χ b
    (closureInclusion j b) (closure_holds χ j hrep b hb hχ)
    isSplitTorus_gm q hD (Dynamic.restrictCocharacter b χ hχ)
    (Dynamic.restrictCocharacter_comp b χ hχ) a (c ≫ a₀)
    (by rw [Category.assoc, ha₀, MonObj.comp_one]) t

end CentralizerProduct

end Langlands.GroupScheme
