import Langlands.GroupScheme.Lie.SubgroupEqualityAlgebra
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Equality near a closed subscheme from its infinitesimal neighbourhoods -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- The union of affine opens on which the ideal of the relative equalizer is zero. -/
def agreementOpen {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y) : X.left.Opens :=
  ⨆ U : {V : X.left.affineOpens // (equalizer.ι f g).left.ker.ideal V = ⊥}, U.1.1

private theorem exists_affineOpen_of_le_ideal_powers {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (h : ∀ n : ℕ, J ≤ I ^ n)
    (x : X) (hx : x ∈ I.support) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ J.ideal V = ⊥ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let A : X.affineOpens := ⟨U, hU⟩
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian A
  obtain ⟨r, hr, hmul⟩ :=
    GroupScheme.Lie.SubgroupEquality.exists_mem_mul_eq_self_of_le_pow
      (I.ideal A) (J.ideal A) (fun n => h n A)
  have hrx : x ∉ X.basicOpen r :=
    (X.mem_zeroLocus_iff _ x).mp ((I.mem_support_iff_of_mem hxU).mp hx) r hr
  have hxOne : x ∈ X.basicOpen (1 - r + r) := by simpa using hxU
  refine ⟨X.affineBasicOpen (1 - r), ((X.basicOpen_add_le (1 - r) r) hxOne).resolve_right hrx, ?_⟩
  let restrict : Γ(X, U) →+* Γ(X, X.basicOpen (1 - r)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (1 - r))).op).hom
  rw [← J.map_ideal_basicOpen A (1 - r)]
  change (J.ideal A).map restrict = ⊥
  apply (Ideal.map_eq_bot_iff_le_ker restrict).mpr
  intro a ha
  have := hU.isLocalization_basicOpen (1 - r)
  change algebraMap Γ(X, U) Γ(X, X.basicOpen (1 - r)) a = 0
  exact (IsLocalization.map_eq_zero_iff (.powers (1 - r)) _ a).mpr
    ⟨⟨1 - r, Submonoid.mem_powers _⟩, by simp [sub_mul, hmul a ha]⟩

private theorem factors_of_ideal_eq_bot {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) (h : J.ideal V = ⊥) :
    ∃ a : V.1.toScheme ⟶ J.subscheme, a ≫ J.subschemeι = V.1.ι := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))
  have hq : Function.Injective (Ideal.Quotient.mk (J.ideal V)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, h])
  have : IsIso q :=
    (ConcreteCategory.isIso_iff_bijective q).mpr ⟨hq, Ideal.Quotient.mk_surjective⟩
  have : IsIso (Spec.map q) := inferInstanceAs (IsIso (Scheme.Spec.map q.op))
  have : IsIso (J.glueDataObjι V) := by
    change IsIso (Spec.map q ≫ V.2.isoSpec.inv)
    infer_instance
  refine ⟨inv (J.glueDataObjι V) ≫ J.subschemeCover.f V, ?_⟩
  rw [Category.assoc, J.subschemeCover_map_subschemeι V, IsIso.inv_hom_id_assoc]

/-- The two maps agree as morphisms of schemes on the open of agreement. -/
theorem agreementOpen_comp_eq {S : Scheme.{u}} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : (agreementOpen f g).ι ≫ f.left = (agreementOpen f g).ι ≫ g.left := by
  let e := equalizer.ι f g
  let J := e.left.ker
  let opens (U : {V : X.left.affineOpens // J.ideal V = ⊥}) : X.left.Opens := U.1.1
  change (⨆ U, opens U).ι ≫ f.left = (⨆ U, opens U).ι ≫ g.left
  apply (Scheme.Opens.iSupOpenCover opens).hom_ext
  intro U
  obtain ⟨a, ha⟩ := factors_of_ideal_eq_bot J U.1 U.2
  have hker : e.left.ker ≤ (opens U).ι.ker := by
    change J ≤ U.1.1.ι.ker
    calc
      J = J.subschemeι.ker := (J.ker_subschemeι).symm
      _ ≤ (a ≫ J.subschemeι).ker := a.le_ker_comp J.subschemeι
      _ = _ := congrArg Scheme.Hom.ker ha
  have he : e.left ≫ f.left = e.left ≫ g.left :=
    congrArg Over.Hom.left (equalizer.condition f g)
  have hloc : (opens U).ι ≫ f.left = (opens U).ι ≫ g.left := by
    rw [← IsClosedImmersion.lift_fac e.left (opens U).ι hker, Category.assoc, Category.assoc, he]
  simpa only [Scheme.Opens.iSupOpenCover, Scheme.homOfLE_ι_assoc] using hloc

/-- Agreement on every infinitesimal neighbourhood puts the zero locus of
the ideal inside the open of agreement. -/
theorem support_subset_agreementOpen_of_eq_on_infinitesimal_neighbourhoods {S : Scheme.{u}}
    {X Y : Over S} [IsLocallyNoetherian X.left] [IsSeparated Y.hom]
    (I : X.left.IdealSheafData) (f g : X ⟶ Y)
    (h : ∀ n : ℕ, (I ^ (n + 1)).subschemeι ≫ f.left = (I ^ (n + 1)).subschemeι ≫ g.left) :
    (I.support : Set X.left) ⊆ (agreementOpen f g : Set X.left) := by
  let e := equalizer.ι f g
  let J := e.left.ker
  have hJ (n : ℕ) : J ≤ I ^ n := by
    cases n with
    | zero =>
      intro V
      change J.ideal V ≤ I.ideal V ^ (0 : ℕ)
      simp
    | succ n =>
      let i := (I ^ (n + 1)).subschemeι
      let j : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
      have hj : j ≫ f = j ≫ g := by
        ext1
        exact h n
      let l := equalizer.lift j hj
      have hl : l.left ≫ e.left = i := congrArg Over.Hom.left (equalizer.lift_ι j hj)
      rw [← Scheme.IdealSheafData.ker_subschemeι (I ^ (n + 1))]
      change J ≤ i.ker
      rw [← hl]
      exact l.left.le_ker_comp e.left
  intro x hx
  obtain ⟨V, hV, hZero⟩ := exists_affineOpen_of_le_ideal_powers I J hJ x hx
  exact Opens.mem_iSup.mpr ⟨⟨V, hZero⟩, hV⟩

/-- Two maps to a separated scheme over the base agree on an open containing
the closed subscheme if they agree on each of its infinitesimal neighbourhoods. -/
theorem exists_open_eq_of_eq_on_infinitesimal_neighbourhoods {S : Scheme.{u}}
    {X Y : Over S} [IsLocallyNoetherian X.left] [IsSeparated Y.hom]
    (I : X.left.IdealSheafData) (f g : X ⟶ Y)
    (h : ∀ n : ℕ, (I ^ (n + 1)).subschemeι ≫ f.left = (I ^ (n + 1)).subschemeι ≫ g.left) :
    ∃ W : X.left.Opens, (I.support : Set X.left) ⊆ (W : Set X.left) ∧
      W.ι ≫ f.left = W.ι ≫ g.left :=
  ⟨agreementOpen f g, support_subset_agreementOpen_of_eq_on_infinitesimal_neighbourhoods I f g h,
    agreementOpen_comp_eq f g⟩

end Langlands.AlgebraicGeometry
