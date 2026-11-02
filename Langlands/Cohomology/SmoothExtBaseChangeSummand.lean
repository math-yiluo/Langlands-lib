import Langlands.Cohomology.SmoothExtBaseChange
import Langlands.Cohomology.HyperextExtBaseChangeSummand
import Langlands.Representation.Induction.PermutationModule

/-!
# Extension of scalars on `Ext` groups of smooth representations: summands and compact induction

`Langlands.Cohomology.SmoothExtBaseChange` proves that, for a localization `S` of `R`, the
comparison map `S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` of smooth representations is
injective or bijective when `X` has a resolution by representations free of finite rank on vectors
fixed by pro-`p` subgroups (`HasProPFreeFixedBasis p`), for `p` invertible in `R` and assuming
`ProPInvariantsExactStatement`. `Langlands.Cohomology.HyperextExtBaseChangeSummand` extends the
general dimension-shifting theorems to resolutions by direct summands of finite sums. This module
combines the two and enlarges the supply of representations in the class.

* `IsSummandOfFiniteSum.map`: additive functors preserve summands of finite sums.
* `IsFreeOnFixedVectors.of_iso`, `HasFreeFixedBasis.of_iso`, `HasProPFreeFixedBasis.of_iso`:
  invariance under isomorphism.
* `isOpen_subgroupOf`, `smoothRestriction_additive`, `smoothCompactInduction_additive`.
* `isFreeOnFixedVectors_smoothCompactInduction`, `HasFreeFixedBasis.smoothCompactInduction`,
  `HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction`,
  `IsSummandOfFiniteSum.smoothCompactInduction`: compact induction `c-Ind_S^G` from an open
  subgroup `S` preserves freeness on `H`-fixed vectors for subgroups `H ≤ S`.
* `compactInductionTrivialIso_hom_unit`, `isFreeOnFixedVectors_smoothPermutation`,
  `hasProPFreeFixedBasis_smoothPermutation`: the permutation representation on `G ⧸ H →₀ M`, for
  `H` open and `M` free, is free on the `H`-fixed vectors with a single basis value at the coset
  `H`.
* `hasProPFreeFixedBasis_compactInduction_permutation` and
  `isSummandOfFiniteSum_biproduct_compactInduction_permutation`: `c-Ind_S^G` of the permutation
  representation on `S ⧸ H →₀ M`, for `H ≤ S` open and pro-`p` and `M` free of finite rank, and
  finite biproducts of such representations (a finite model of Harris's `(4.4.4)`).
* `smoothExtBaseChangeMap_injective_of_hasResolutionBy_summand`,
  `smoothExtBaseChangeMap_bijective_of_hasResolutionBy_summand`,
  `smoothExtBaseChangeEquivOfHasResolutionBySummand`: the comparison theorems for resolutions by
  summands of finite sums of representations in `HasProPFreeFixedBasis p`.

The existence of the resolutions remains a hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

universe w uR uS uG uV uC vC uD vD t t'

namespace HyperextScalarExtension

section Map

variable {C : Type uC} [Category.{vC} C] [Preadditive C] {D : Type uD} [Category.{vD} D]
  [Preadditive D] {Q : C → Prop} {Q' : D → Prop}

/-- An additive functor sending objects satisfying `Q` to objects satisfying `Q'` sends summands
of finite sums of objects satisfying `Q` to summands of finite sums of objects satisfying `Q'`. -/
theorem IsSummandOfFiniteSum.map (F : C ⥤ D) [F.Additive] (hF : ∀ P, Q P → Q' (F.obj P)) {X : C}
    (hX : IsSummandOfFiniteSum Q X) : IsSummandOfFiniteSum Q' (F.obj X) := by
  obtain ⟨ι, _, P, a, b, hP, hab⟩ := hX
  refine ⟨ι, inferInstance, fun i => F.obj (P i), fun i => F.map (a i), fun i => F.map (b i),
    fun i => hF _ (hP i), ?_⟩
  rw [← CategoryTheory.Functor.map_id, ← hab, F.map_sum]
  simp only [CategoryTheory.Functor.map_comp]

end Map

section Iso

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Freeness on fixed vectors is transported along isomorphisms of smooth representations. -/
theorem IsFreeOnFixedVectors.of_iso {H : Subgroup G} {P P' : SmoothRep.{uR, uG, w} R G}
    (e : P ≅ P') {ι : Type*} {x : ι → P} (hx : IsFreeOnFixedVectors H x) :
    IsFreeOnFixedVectors H (fun i => SmoothRep.hom e.hom (x i)) where
  mem_invariants i := smoothRepHom_mem_invariants H e.hom (hx.mem_invariants i)
  hom_ext {Y f g} hfg := (cancel_epi e.hom).1 (hx.hom_ext fun i => hfg i)
  exists_hom {Y} y hy := by
    obtain ⟨f, hf⟩ := hx.exists_hom y hy
    refine ⟨e.inv ≫ f, fun i => ?_⟩
    have h : SmoothRep.hom e.inv (SmoothRep.hom e.hom (x i)) = x i :=
      congrArg (fun T => SmoothRep.hom T (x i)) e.hom_inv_id
    exact (congrArg (SmoothRep.hom f) h).trans (hf i)

/-- Being free of finite rank on `H`-fixed vectors is invariant under isomorphism. -/
theorem HasFreeFixedBasis.of_iso {H : Subgroup G} {P P' : SmoothRep.{uR, uG, w} R G}
    (e : P ≅ P') (hP : HasFreeFixedBasis H P) : HasFreeFixedBasis H P' := by
  obtain ⟨n, x, hx⟩ := hP
  exact ⟨n, _, hx.of_iso e⟩

/-- Being free of finite rank on vectors fixed by a pro-`p` subgroup is invariant under
isomorphism. -/
theorem HasProPFreeFixedBasis.of_iso {p : ℕ} {P P' : SmoothRep.{uR, uG, w} R G}
    (e : P ≅ P') (hP : HasProPFreeFixedBasis p P) : HasProPFreeFixedBasis p P' := by
  obtain ⟨H, hH, hPH⟩ := hP
  exact ⟨H, hH, hPH.of_iso e⟩

end Iso

section CompactInduction

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- For subgroups `H ≤ S` with `H` open in `G`, the subgroup `H.subgroupOf S` of `S` is open. -/
theorem isOpen_subgroupOf {H : Subgroup G} (hH : IsOpen (H : Set G)) (S : Subgroup G) :
    IsOpen ((H.subgroupOf S : Subgroup S) : Set S) := by
  rw [Subgroup.coe_subgroupOf]
  exact hH.preimage continuous_subtype_val

variable (R) in
/-- Restriction of smooth representations to a subgroup is additive. -/
instance smoothRestriction_additive (S : Subgroup G) :
    (Induction.smoothRestriction.{uR, uG, uV} R S).Additive where
  map_add := rfl

/-- Compact induction from an open subgroup is additive (it is a left adjoint of the additive
restriction functor). -/
theorem smoothCompactInduction_additive (S : Subgroup G) (hS : IsOpen (S : Set G)) :
    (Induction.smoothCompactInduction.{uR, uG, uV} R S).Additive :=
  (Induction.compactInductionAdjunction.{uR, uG, uV} (R := R) S hS).left_adjoint_additive

variable (S : Subgroup G) (hS : IsOpen (S : Set G))

/-- **Compact induction preserves freeness on fixed vectors.** Let `S` be an open subgroup of `G`
and `H ≤ S` a subgroup. If the family `x` of a smooth representation `V` of `S` is free on
`H`-fixed vectors (for `H` viewed as the subgroup `H.subgroupOf S` of `S`), then the images of
the `x i` under the unit `V → c-Ind_S^G V` of Frobenius reciprocity are free on `H`-fixed
vectors of `c-Ind_S^G V`. -/
theorem isFreeOnFixedVectors_smoothCompactInduction {H : Subgroup G} (hHS : H ≤ S)
    {V : SmoothRep.{uR, uG, max uG uV} R S} {ι : Type*} {x : ι → V}
    (hx : IsFreeOnFixedVectors (H.subgroupOf S) x) :
    IsFreeOnFixedVectors H (P := (Induction.smoothCompactInduction.{uR, uG, uV} R S).obj V)
      (fun i => SmoothRep.hom
        ((Induction.compactInductionAdjunction.{uR, uG, uV} S hS).unit.app V) (x i)) where
  mem_invariants i := (Representation.mem_invariants _ _).2 fun h => by
    have hv := (Representation.mem_invariants _ _).1 (hx.mem_invariants i)
      ⟨⟨(h : G), hHS h.2⟩, h.2⟩
    have hu := Representation.IntertwiningMap.isIntertwining _ _
      (SmoothRep.hom ((Induction.compactInductionAdjunction.{uR, uG, uV} S hS).unit.app V))
      ⟨(h : G), hHS h.2⟩ (x i)
    exact hu.symm.trans (congrArg (SmoothRep.hom
      ((Induction.compactInductionAdjunction.{uR, uG, uV} S hS).unit.app V)) hv)
  hom_ext {Y f g} hfg := by
    let adj := Induction.compactInductionAdjunction.{uR, uG, uV} (R := R) S hS
    exact (adj.homEquiv V Y).injective (hx.hom_ext fun i => hfg i)
  exists_hom {Y} y hy := by
    let adj := Induction.compactInductionAdjunction.{uR, uG, uV} (R := R) S hS
    let Y' := (Induction.smoothRestriction.{uR, uG, max uG uV} R S).obj Y
    let y' : ι → Y' := y
    have hy' : ∀ i, y' i ∈ Representation.invariants
        (Y'.representation.comp (H.subgroupOf S).subtype) := fun i =>
      (Representation.mem_invariants _ _).2 fun h =>
        (Representation.mem_invariants _ _).1 (hy i) ⟨((h : S) : G), h.2⟩
    obtain ⟨f, hf⟩ := hx.exists_hom y' hy'
    refine ⟨(adj.homEquiv V Y).symm f, fun i => ?_⟩
    have h := congrArg (fun T => SmoothRep.hom T (x i)) ((adj.homEquiv V Y).apply_symm_apply f)
    exact h.trans (hf i)

include hS in
/-- Compact induction from an open subgroup `S` sends representations free of finite rank on
`H`-fixed vectors, `H ≤ S`, to representations free of finite rank on `H`-fixed vectors. -/
theorem HasFreeFixedBasis.smoothCompactInduction {H : Subgroup G} (hHS : H ≤ S)
    {V : SmoothRep.{uR, uG, max uG uV} R S} (hV : HasFreeFixedBasis (H.subgroupOf S) V) :
    HasFreeFixedBasis H ((Induction.smoothCompactInduction.{uR, uG, uV} R S).obj V) := by
  obtain ⟨n, x, hx⟩ := hV
  exact ⟨n, _, isFreeOnFixedVectors_smoothCompactInduction S hS hHS hx⟩

include hS in
/-- Compact induction from an open subgroup `S` sends representations free of finite rank on
vectors fixed by a pro-`p` subgroup `H ≤ S` to representations free of finite rank on vectors
fixed by a pro-`p` subgroup of `G`. -/
theorem HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction {p : ℕ}
    {H : Subgroup G} (hHp : IsProPSubgroup p H) (hHS : H ≤ S)
    {V : SmoothRep.{uR, uG, max uG uV} R S} (hV : HasFreeFixedBasis (H.subgroupOf S) V) :
    HasProPFreeFixedBasis p ((Induction.smoothCompactInduction.{uR, uG, uV} R S).obj V) :=
  ⟨H, hHp, hV.smoothCompactInduction S hS hHS⟩

include hS in
/-- Compact induction from an open subgroup `S` sends summands of finite sums of representations
free of finite rank on vectors fixed by `H.subgroupOf S`, for a pro-`p` subgroup `H ≤ S`, to
summands of finite sums of representations free of finite rank on vectors fixed by a pro-`p`
subgroup. -/
theorem IsSummandOfFiniteSum.smoothCompactInduction {p : ℕ} {H : Subgroup G}
    (hHp : IsProPSubgroup p H) (hHS : H ≤ S) {V : SmoothRep.{uR, uG, max uG uV} R S}
    (hV : IsSummandOfFiniteSum (HasFreeFixedBasis (H.subgroupOf S)) V) :
    IsSummandOfFiniteSum (HasProPFreeFixedBasis p)
      ((Induction.smoothCompactInduction.{uR, uG, uV} R S).obj V) :=
  have := smoothCompactInduction_additive (R := R) S hS
  hV.map _ fun _ hP => hP.hasProPFreeFixedBasis_smoothCompactInduction S hS hHp hHS

end CompactInduction

section Permutation

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The unit of Frobenius reciprocity for the trivial representation on `M`, followed by the
identification of `c-Ind_H^G M` with the permutation representation on `G ⧸ H`, sends `v` to the
function with single value `v` at the coset `H`. -/
theorem compactInductionTrivialIso_hom_unit (M : Type (max uG uV)) [AddCommGroup M] [Module R M]
    (v : M) :
    SmoothRep.hom (Induction.compactInductionTrivialIso R M H hH).hom
      (SmoothRep.hom ((Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
        ((smoothTrivialFunctor R H).obj (ModuleCat.of R M))) v) =
      Finsupp.single (QuotientGroup.mk 1 : G ⧸ H) v := by
  classical
  refine Finsupp.ext fun q => QuotientGroup.induction_on q fun y => ?_
  change Induction.eval H _ (Induction.unitFunction H hH _
    ((smoothTrivialFunctor R H).obj (ModuleCat.of R M)).isSmooth v).1 y⁻¹ = _
  erw [Induction.eval_unitFunction]
  rw [Finsupp.single_apply]
  by_cases hy : y ∈ H
  · have hy' : y⁻¹ ∈ H := H.inv_mem hy
    have h1 : (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk y :=
      QuotientGroup.eq.2 (by simpa using hy)
    simp only [hy', ↓reduceDIte, h1, ↓reduceIte]
    rfl
  · have hy' : y⁻¹ ∉ H := fun h => hy (by simpa using H.inv_mem h)
    have h1 : (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk y := fun h =>
      hy (by simpa using QuotientGroup.eq.1 h)
    simp only [hy', ↓reduceDIte, h1, ↓reduceIte]
    rfl

/-- **Permutation representations are free on fixed vectors.** For an open subgroup `H` and an
`R`-module `M` with a basis `b`, the permutation representation of `G` on `G ⧸ H →₀ M` (the
permutation `R[G]`-module on the coset set `G ⧸ H` with coefficients `M`, that is `R[G ⧸ H] ⊗[R] M`
with `R[G ⧸ H]` the free `R`-module on the cosets; a module over the quotient group ring only
when `H` is normal) is free on the `H`-fixed vectors `δ_H ⊗ b i`, the functions with single
value `b i` at the coset `H`. -/
theorem isFreeOnFixedVectors_smoothPermutation (M : Type (max uG uV)) [AddCommGroup M]
    [Module R M] {ι : Type*} (b : Module.Basis ι R M) :
    IsFreeOnFixedVectors H (P := Induction.smoothPermutation R M H hH)
      (fun i => Finsupp.single (QuotientGroup.mk 1 : G ⧸ H) (b i)) := by
  have h := (isFreeOnFixedVectors_compactInduction.{uR, uG, uV} H hH (ModuleCat.of R M) b).of_iso
    (Induction.compactInductionTrivialIso R M H hH)
  have e : (fun i => SmoothRep.hom (Induction.compactInductionTrivialIso R M H hH).hom
      (SmoothRep.hom ((Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
        ((smoothTrivialFunctor R H).obj (ModuleCat.of R M))) (b i))) =
      fun i => Finsupp.single (QuotientGroup.mk 1 : G ⧸ H) (b i) :=
    funext fun i => compactInductionTrivialIso_hom_unit H hH M (b i)
  exact e ▸ h

include hH in
/-- For an open pro-`p` subgroup `H` and an `R`-module `M` with a basis indexed by `Fin n`, the
permutation representation on `G ⧸ H →₀ M` is free of finite rank on vectors fixed by a pro-`p`
subgroup. -/
theorem hasProPFreeFixedBasis_smoothPermutation {p : ℕ} (hHp : IsProPSubgroup p H)
    (M : Type (max uG uV)) [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    HasProPFreeFixedBasis p (Induction.smoothPermutation R M H hH) :=
  ⟨H, hHp, n, _, isFreeOnFixedVectors_smoothPermutation.{uR, uG, uV} H hH M b⟩

/-- **Compact induction of permutation modules (for `H` normal in `S`, Harris's
`c-Ind_{S(ẽ)}^{GJ}` of free `𝒪[S(ẽ)/H]`-modules).** Let `H ≤ S` be subgroups of `G` with `H`
open and pro-`p`, and let `M` be an `R`-module with a basis indexed by `Fin n`. Then the compact
induction `c-Ind_S^G` of the permutation representation of `S` on `S ⧸ H →₀ M` (the permutation
`R[S]`-module on the coset set `S ⧸ H` with coefficients `M`, that is `R[S ⧸ H] ⊗[R] M` with
`R[S ⧸ H]` the free `R`-module on the cosets; a free module over the quotient group ring
`R[S ⧸ H]` only when `H` is normal in `S`) is free of finite rank on vectors fixed by a pro-`p`
subgroup. -/
theorem hasProPFreeFixedBasis_compactInduction_permutation (S : Subgroup G) {p : ℕ}
    {H : Subgroup G} (hHp : IsProPSubgroup p H) (hH : IsOpen (H : Set G)) (hHS : H ≤ S)
    (M : Type (max uG uV)) [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    HasProPFreeFixedBasis p ((Induction.smoothCompactInduction.{uR, uG, uV} R S).obj
      (Induction.smoothPermutation R M (H.subgroupOf S) (isOpen_subgroupOf hH S))) :=
  HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction S
    (Subgroup.isOpen_mono hHS hH) hHp hHS
    ⟨n, _, isFreeOnFixedVectors_smoothPermutation.{uR, uG, uV} (H.subgroupOf S)
      (isOpen_subgroupOf hH S) M b⟩

/-- **Finite sums of compactly induced permutation modules (Harris's `(4.4.4)`, finite case).**
For a finite family of subgroups `H j ≤ S j` of `G` with `H j` open and pro-`p`, and of
`R`-modules `M j` with bases indexed by `Fin (n j)`, the biproduct of the compact inductions
`c-Ind_{S j}^G` of the permutation representations of `S j` on `S j ⧸ H j →₀ M j` is a summand of
a finite sum of representations free of finite rank on vectors fixed by pro-`p` subgroups. -/
theorem isSummandOfFiniteSum_biproduct_compactInduction_permutation {J : Type} [Fintype J]
    (S : J → Subgroup G) {p : ℕ} {H : J → Subgroup G} (hHp : ∀ j, IsProPSubgroup p (H j))
    (hH : ∀ j, IsOpen (H j : Set G)) (hHS : ∀ j, H j ≤ S j)
    (M : J → Type (max uG uV)) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] {n : J → ℕ}
    (b : ∀ j, Module.Basis (Fin (n j)) R (M j))
    [HasBiproduct fun j => (Induction.smoothCompactInduction.{uR, uG, uV} R (S j)).obj
      (Induction.smoothPermutation R (M j) ((H j).subgroupOf (S j))
        (isOpen_subgroupOf (hH j) (S j)))] :
    IsSummandOfFiniteSum (HasProPFreeFixedBasis p)
      (⨁ fun j => (Induction.smoothCompactInduction.{uR, uG, uV} R (S j)).obj
        (Induction.smoothPermutation R (M j) ((H j).subgroupOf (S j))
          (isOpen_subgroupOf (hH j) (S j)))) :=
  IsSummandOfFiniteSum.biproduct _ fun j => IsSummandOfFiniteSum.of_prop
    (hasProPFreeFixedBasis_compactInduction_permutation.{uR, uG, uV} (S j) (hHp j) (hH j)
      (hHS j) (M j) (b j))

end Permutation

section Localization

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Module.Flat R S] [HasExt.{t} (SmoothRep.{uR, uG, max uS w} R G)]
  [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)] (Y : SmoothRep.{uR, uG, max uS w} R G)

include M

/-- **`Ext` of smooth representations and localization, injectivity, with summands.** Assume
`ProPInvariantsExactStatement`, let `p` be invertible in `R` and let `S` be a localization of
`R`. If `X` has a resolution `P_n → ⋯ → P_0 → X → 0` by direct summands of finite direct sums of
smooth representations free of finite rank on vectors fixed by pro-`p` subgroups, then
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is injective. -/
theorem smoothExtBaseChangeMap_injective_of_hasResolutionBy_summand
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum (HasProPFreeFixedBasis p)) n X) :
    Function.Injective (smoothExtBaseChangeMap.{max uS w} R S G X Y n) :=
  extBaseChangeMap_injective_of_hasResolutionBy_summand (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

/-- **`Ext` of smooth representations and localization, with summands.** Assume
`ProPInvariantsExactStatement`, let `p` be invertible in `R` and let `S` be a localization of
`R`. If `X` has a resolution `P_{n+1} → ⋯ → P_0 → X → 0` by direct summands of finite direct sums
of smooth representations free of finite rank on vectors fixed by pro-`p` subgroups, then
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is bijective. -/
theorem smoothExtBaseChangeMap_bijective_of_hasResolutionBy_summand
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum (HasProPFreeFixedBasis p)) (n + 1) X) :
    Function.Bijective (smoothExtBaseChangeMap.{max uS w} R S G X Y n) :=
  extBaseChangeMap_bijective_of_hasResolutionBy_summand (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

/-- Under the hypotheses of `smoothExtBaseChangeMap_bijective_of_hasResolutionBy_summand`, the
`S`-linear equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` given by
`smoothExtBaseChangeMap`. -/
def smoothExtBaseChangeEquivOfHasResolutionBySummand
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum (HasProPFreeFixedBasis p)) (n + 1) X) :
    S ⊗[R] Abelian.Ext.{t} X Y n ≃ₗ[S]
      Abelian.Ext.{t'} ((smoothRepExtendScalars.{max uS w} R S G).obj X)
        ((smoothRepExtendScalars.{max uS w} R S G).obj Y) n :=
  extBaseChangeEquivOfHasResolutionBySummand (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

@[simp]
theorem smoothExtBaseChangeEquivOfHasResolutionBySummand_apply
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (IsSummandOfFiniteSum (HasProPFreeFixedBasis p)) (n + 1) X)
    (z : S ⊗[R] Abelian.Ext.{t} X Y n) :
    smoothExtBaseChangeEquivOfHasResolutionBySummand.{w} S M Y hP hR n hX z =
      smoothExtBaseChangeMap.{max uS w} R S G X Y n z :=
  rfl

end Localization

end HyperextScalarExtension

end Langlands.Cohomology
