import Langlands.Geometry.Building.LeviSpecialPointRestrictionStatement
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Proof of the KP §6.7.2 affine-root and special-point restriction statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Geometry.Building

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

/-- Apartment data are determined by their equipollence class. -/
theorem eq_of_carrier_eq {D₁ D₂ : KPApartmentData i ω} (h : D₁.carrier = D₂.carrier) :
    D₁ = D₂ := by
  cases D₁
  cases D₂
  cases h
  rfl

/-- Two apartment data with a common point are equal. -/
theorem eq_of_apartment_val_eq {D₁ D₂ : KPApartmentData i ω} (x₁ : D₁.Apartment)
    (x₂ : D₂.Apartment) (h : x₁.val = x₂.val) : D₁ = D₂ :=
  eq_of_carrier_eq (Set.ext fun φ => by
    rw [D₁.mem_iff_equipollent x₁.mem, D₂.mem_iff_equipollent x₂.mem, h])

variable (D : KPApartmentData i ω)

/-- A filtration jump in a root direction `b` yields an ordinary affine root `2^m e`,
provided `2^n b` is not a root for some `n`. -/
theorem exists_two_pow_smul_mem_affineRoots :
    ∀ (n : ℕ) (b : relativeRoots i) (e : D.Apartment →ᵃ[ℝ] ℝ),
      e.linear = rootForm i b → D.affineRootGroupPlus b e ≠ D.affineRootGroup b e →
      (2 ^ n) • (b : characterLattice S) ∉ relativeRoots i →
      ∃ m : ℕ, (2 : ℝ) ^ m • e ∈ D.affineRoots := by
  intro n
  induction n with
  | zero =>
    intro b e _ _ hn
    exact absurd (by simpa only [pow_zero, one_smul] using b.property) hn
  | succ n ih =>
    intro b e hlin hjump hn
    by_cases he : e ∈ D.affineRoots
    · exact ⟨0, by simpa only [pow_zero, one_smul] using he⟩
    have h2b : 2 • (b : characterLattice S) ∈ relativeRoots i := by
      by_contra h2b
      exact he (D.mem_affineRoots_of_not_double_root h2b hlin hjump)
    have hlin2 : ((2 : ℝ) • e).linear = rootForm i ⟨2 • (b : characterLattice S), h2b⟩ := by
      rw [AffineMap.smul_linear, hlin, rootForm_nsmul b.property 2 h2b]
      norm_num
    have hjump2 := D.affineRootGroupPlus_double_ne_of_not_mem_affineRoots h2b hlin hjump he
    have hn2 : (2 ^ n) • (2 • (b : characterLattice S)) ∉ relativeRoots i := by
      rwa [smul_smul, ← pow_succ]
    obtain ⟨m, hm⟩ := ih ⟨2 • (b : characterLattice S), h2b⟩ ((2 : ℝ) • e) hlin2 hjump2 hn2
    exact ⟨m + 1, by rwa [smul_smul, ← pow_succ] at hm⟩

omit [Mono i.hom.hom.left] in
/-- For a split torus with finitely many roots, some `2^n a` is not a root. -/
theorem exists_two_pow_smul_not_mem_relativeRoots (hS : IsSplitTorus S.toGrp)
    (hfin : (relativeRoots i).Finite) (a : relativeRoots i) :
    ∃ n : ℕ, (2 ^ n) • (a : characterLattice S) ∉ relativeRoots i := by
  have hfinset : {n : ℕ | (2 ^ n) • (a : characterLattice S) ∈ relativeRoots i}.Finite := by
    refine Set.Finite.of_finite_image
      (f := fun n : ℕ => (2 ^ n) • (a : characterLattice S)) (hfin.subset ?_) ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hn
    · intro n hn m hm hnm
      have h := congrArg (rootForm i)
        (Subtype.ext hnm : (⟨_, hn⟩ : relativeRoots i) = ⟨_, hm⟩)
      rw [rootForm_nsmul a.property _ hn, rootForm_nsmul a.property _ hm] at h
      have h' := smul_left_injective ℝ
        (Langlands.BruhatTits.SpecialCompact.rootForm_ne_zero_of_split hS i a) h
      exact Nat.pow_right_injective le_rfl (by exact_mod_cast h')
  exact Set.Finite.exists_notMem hfinset

/-- Axiom V 0 and the doubling argument: every root direction of a split torus with
finitely many roots is, up to a nonzero factor, the derivative of an ordinary affine root. -/
theorem exists_affineRoot_linear_eq_smul_rootForm (hS : IsSplitTorus S.toGrp)
    (hfin : (relativeRoots i).Finite) (a : relativeRoots i) :
    ∃ ψ ∈ D.affineRoots, ∃ c : ℝ, c ≠ 0 ∧ ψ.linear = c • rootForm i a := by
  let x : D.Apartment := Classical.arbitrary _
  obtain ⟨u, hu, hne⟩ := x.isValuation.exists_ne_top a.property
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨b, hb, hjump⟩ := D.affineFunctional_mem_extendedAffineRoots (a := a) hu ht.symm
  have hba : b = a := Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split hS i
    (hb.symm.trans (affineFunctional_linear a x t))
  subst hba
  obtain ⟨n, hn⟩ := exists_two_pow_smul_not_mem_relativeRoots hS hfin b
  obtain ⟨m, hm⟩ := D.exists_two_pow_smul_mem_affineRoots n b _ hb hjump hn
  exact ⟨_, hm, (2 : ℝ) ^ m, pow_ne_zero _ two_ne_zero, by rw [AffineMap.smul_linear, hb]⟩

/-- A special point is a vertex once every root direction is, up to a nonzero factor, the
derivative of an ordinary affine root (the argument of KP Proposition 1.3.43(3)). -/
theorem isVertex_of_isSpecialPoint_of_rootDirections (hS : IsSplitTorus S.toGrp)
    (hdir : ∀ a : relativeRoots i,
      ∃ ψ ∈ D.affineRoots, ∃ c : ℝ, c ≠ 0 ∧ ψ.linear = c • rootForm i a)
    {x : D.Apartment} (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    AffineRootSystem.IsVertex D.affineRoots x := by
  apply Set.Subset.antisymm
  · intro y hy
    apply Set.mem_singleton_iff.mpr
    apply vsub_eq_zero_iff_eq.mp
    apply eq_zero_of_rootForm_eq_zero i
    intro a
    obtain ⟨ψ, hψ, c, hc, hlin⟩ := hdir a
    obtain ⟨φ, hφ, hker⟩ := (AffineRootSystem.isSpecialPoint_iff_ker
      (fun _ h => Langlands.BruhatTits.SpecialCompact.affineRoot_linear_ne_zero_of_split
        hS i D h) x).mp hx ψ hψ
    have hφy : φ y = 0 := AffineRootSystem.facet_subset_hyperplane hφ hy
    have h0 : ψ.linear (y -ᵥ x) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker, LinearMap.mem_ker, AffineMap.linearMap_vsub]
      change φ y - φ x = 0
      rw [hφy, hφ.2, sub_self]
    rw [hlin, LinearMap.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc
  · exact Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self D.affineRoots x)

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.SpecialCompact

section Restriction

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G} {i : S.toGrp ⟶ G}
  {iM : S.toGrp ⟶ M} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] [Mono iM.hom.hom.left]
  [IsAffineHom M.X.hom] {ω : kˣ → ℝ} {D : KPApartmentData i ω}

/-- Two restrictions of the same point have the same valuation: they agree on the roots of
`M` by definition and are `⊤` off them. -/
theorem IsLeviRestriction.val_eq_val {DM₁ DM₂ : KPApartmentData iM ω} {x : D.Apartment}
    {y₁ : DM₁.Apartment} {y₂ : DM₂.Apartment} (h₁ : IsLeviRestriction j x y₁)
    (h₂ : IsLeviRestriction j x y₂) : y₁.val = y₂.val := by
  ext a m
  by_cases ha : a ∈ relativeRoots iM
  · rw [h₁ a ha m, h₂ a ha m]
  · rw [y₁.isValuation.eq_top_of_not_mem_roots a ha m,
      y₂.isValuation.eq_top_of_not_mem_roots a ha m]

end Restriction

section Levi

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ω : Fˣ → ℝ} (D : KPApartmentData i ω)

local notation "R" => leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D
local notation "π" => leviApartmentAffineProjection hS i iM j hcomp ζ hj hjc hG hi D

/-- Levi apartment data containing one restriction of a point of `D` are the restricted
class `leviRestrictedApartmentData`. -/
theorem eq_leviRestrictedApartmentData {DM : KPApartmentData iM ω} {x₀ : D.Apartment}
    {xM₀ : DM.Apartment} (h₀ : IsLeviRestriction j x₀ xM₀) : DM = R :=
  KPApartmentData.eq_of_apartment_val_eq xM₀
    (leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x₀)
    (h₀.val_eq_val
      (isLeviRestriction_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x₀))

include hS hcomp hj hjc hG hi in
/-- KP §6.7.2 for Levi apartment data containing one restriction of a point of `D`. -/
theorem leviSpecialPointRestriction_of_isLeviRestriction (DM : KPApartmentData iM ω)
    (x₀ : D.Apartment) (xM₀ : DM.Apartment) (h₀ : IsLeviRestriction j x₀ xM₀) :
    (∀ ψM ∈ DM.affineRoots, ∃ ψ ∈ D.affineRoots,
      ∀ (x : D.Apartment) (xM : DM.Apartment), IsLeviRestriction j x xM → ψ x = ψM xM) ∧
    (∀ ψM ∈ DM.extendedAffineRoots, ∃ ψ ∈ D.extendedAffineRoots,
      ∀ (x : D.Apartment) (xM : DM.Apartment), IsLeviRestriction j x xM → ψ x = ψM xM) ∧
    ∀ (x : D.Apartment) (xM : DM.Apartment), IsLeviRestriction j x xM →
      AffineRootSystem.IsSpecialPoint D.affineRoots x →
        AffineRootSystem.IsSpecialPoint DM.affineRoots xM ∧
          AffineRootSystem.IsVertex DM.affineRoots xM := by
  obtain rfl := eq_leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D h₀
  have hpt : ∀ (x : D.Apartment) (xM : (R).Apartment), IsLeviRestriction j x xM →
      xM = π x := fun x xM h =>
    KPApartmentData.Apartment.ext (h.val_eq_val
      (isLeviRestriction_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D x))
  refine ⟨fun ψM hψM => ⟨leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψM,
      leviAffineRootPullback_mem_affineRoots hS i iM j hcomp ζ hj hjc hG hi D hψM,
      fun x xM h => by rw [hpt x xM h]; rfl⟩,
    fun ψM hψM => ⟨leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψM,
      leviAffineRootPullback_mem_extendedAffineRoots hS i iM j hcomp ζ hj hjc hG hi D hψM,
      fun x xM h => by rw [hpt x xM h]; rfl⟩,
    fun x xM h hx => ?_⟩
  obtain rfl := hpt x xM h
  have hs := isSpecialPoint_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D hx
  exact ⟨hs, (R).isVertex_of_isSpecialPoint_of_rootDirections hS
    (fun a => (R).exists_affineRoot_linear_eq_smul_rootForm hS (hS.finite_relativeRoots iM) a)
    hs⟩

end Levi

end Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

open Langlands.BruhatTits.SpecialCompact

/-- Kaletha–Prasad §6.7.2 for the actual standard Levi subgroups. -/
theorem leviSpecialPointRestriction : LeviSpecialPointRestrictionStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  intro hν J hJ
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
  rintro D DM ⟨x₀, xM₀, h₀⟩
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  let : Smooth (Standard.leviScheme i ν J).X.hom := hM.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hj := Standard.isRepresentedBy_leviHom i ν J
  rw [(hcompare ζ hζ).2.1] at hj
  exact leviSpecialPointRestriction_of_isLeviRestriction hi.isSplitSubtorus.1 i
    (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
    (Standard.leviTorusHom_comp i ν J) ζ hj (Standard.isClosedSubgroup_leviHom i ν J) hG hi
    D DM x₀ xM₀ h₀

end Langlands.Geometry.Building
