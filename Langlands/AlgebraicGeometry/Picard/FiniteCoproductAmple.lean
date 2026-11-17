import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleAmpleCover
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Ampleness on finite disjoint unions of schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace FiniteCoproduct

/-- A coproduct component is closed as well as open, in any universe. -/
theorem isClosedImmersion_ι {I : Type u} (X : I → Scheme.{u}) (i : I) :
    IsClosedImmersion (Sigma.ι X i) := by
  apply IsClosedImmersion.of_isPreimmersion
  have heq : (Set.range (Sigma.ι X i))ᶜ =
      ⋃ j : {j : I // j ≠ i}, Set.range (Sigma.ι X j.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, y, hy⟩ := (sigmaOpenCover X).exists_eq x
      have hj : j ≠ i := by
        rintro rfl
        exact hx ⟨y, hy⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, y, hy⟩
    · intro hx
      obtain ⟨⟨j, hj⟩, y, hy⟩ := Set.mem_iUnion.mp hx
      rintro ⟨z, hz⟩
      have : i = j := congrArg Sigma.fst
        ((sigmaι_eq_iff X i j z y).mp (hz.trans hy.symm))
      exact hj this.symm
  rw [← isOpen_compl_iff, heq]
  exact isOpen_iUnion fun j => (Sigma.ι X j.1).isOpenEmbedding.isOpen_range

variable {I : Type u} (X Y : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y i)

/-- A component square of the coproduct of scheme morphisms is cartesian. -/
theorem isPullback_component (i : I) :
    IsPullback (Sigma.ι X i) (f i)
      (Sigma.desc fun j => f j ≫ Sigma.ι Y j) (Sigma.ι Y i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  ext x
  obtain ⟨j, z, rfl⟩ := (sigmaOpenCover X).exists_eq x
  have hr (T : I → Scheme.{u}) (a b : I) (w : T b) :
      Sigma.ι T b w ∈ Set.range (Sigma.ι T a) ↔ a = b := by
    constructor
    · rintro ⟨v, hv⟩
      exact congrArg Sigma.fst ((sigmaι_eq_iff T a b v w).mp hv)
    · rintro rfl
      exact ⟨w, rfl⟩
  change (Sigma.ι X j ≫ (Sigma.desc fun k => f k ≫ Sigma.ι Y k)) z ∈
      Set.range (Sigma.ι Y i) ↔ Sigma.ι X j z ∈ Set.range (Sigma.ι X i)
  rw [Sigma.ι_comp_desc]
  change Sigma.ι Y j (f j z) ∈ Set.range (Sigma.ι Y i) ↔ _
  rw [hr, hr]

/-- The actual pullback of the coproduct map to a component of its target. -/
def componentPullbackIso (i : I) :
    X i ≅ pullback (Sigma.desc fun j => f j ≫ Sigma.ι Y j) (Sigma.ι Y i) :=
  (isPullback_component X Y f i).isoPullback

end FiniteCoproduct

namespace LineBundle

/-- Ampleness of the restrictions to all components gives ampleness on a finite
coproduct, provided the coproduct is compact and quasi-separated. -/
theorem isAmple_of_finite_coproduct {I : Type u} [Finite I]
    (X : I → Scheme.{u}) [CompactSpace (∐ X : Scheme.{u})]
    [QuasiSeparatedSpace (∐ X : Scheme.{u})] (L : LineBundle (∐ X))
    (hL : ∀ i, ((pullback (Sigma.ι X i)).obj L).IsAmple) : L.IsAmple := by
  let Y : I → Scheme.{u} := fun i => Spec Γ(X i, ⊤)
  let q : ∀ i, X i ⟶ Y i := fun i => (X i).toSpecΓ
  let p : (∐ X) ⟶ ∐ Y := Sigma.desc fun i => q i ≫ Sigma.ι Y i
  apply L.isAmple_of_affine_base_openCover p (sigmaOpenCover Y)
  intro i
  let h := FiniteCoproduct.isPullback_component X Y q i
  let e := h.isoPullback
  have hc : e.inv ≫ Sigma.ι X i = Limits.pullback.fst p (Sigma.ι Y i) := by
    rw [← h.isoPullback_hom_fst]
    simp [e, p]
  exact ((hL i).pullback_of_isAffineHom e.inv).of_iso
    ((Scheme.Modules.pullbackComp e.inv (Sigma.ι X i)).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr hc).app L.obj)

/-- Ampleness on a finite coproduct is equivalent to ampleness on every
component, with no nonemptiness assumption on the index. -/
theorem isAmple_finite_coproduct_iff {I : Type u} [Finite I]
    (X : I → Scheme.{u}) [CompactSpace (∐ X : Scheme.{u})]
    [QuasiSeparatedSpace (∐ X : Scheme.{u})] (L : LineBundle (∐ X)) :
    L.IsAmple ↔ ∀ i, ((pullback (Sigma.ι X i)).obj L).IsAmple := by
  constructor
  · intro hL i
    let := FiniteCoproduct.isClosedImmersion_ι X i
    exact hL.pullback_of_isAffineHom (Sigma.ι X i)
  · exact isAmple_of_finite_coproduct X L

end LineBundle

end Langlands.AlgebraicGeometry.Picard
