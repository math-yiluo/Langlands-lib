import Langlands.Cohomology.SmoothExtBaseChangeSummand
import Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit

/-!
# Free invariants of smooth representations and the smooth `Ext` comparison class

This module connects the Library's free invariants and direct limits of free modules over
quotient group algebras (`IsFreeOnInvariants`, `IsFreeLimit` from
`Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit`) with the class of representations used
by the Library's comparison theorems for extension of scalars on `Ext` groups of smooth
representations (`HasFreeFixedBasis`, `HasProPFreeFixedBasis`, `IsSummandOfFiniteSum` from
`Langlands.Cohomology.SmoothExtBaseChangeSummand`).

For an open normal subgroup `H` of a topological group `G` and a smooth representation `V`,
`smoothInvariantsInflation V H hH` is the smooth representation of `G` on the `H`-invariants of
`V`. If these invariants are a free `R[G ⧸ H]`-module (`IsFreeOnInvariants`) that is finitely
generated over `R`, then they are isomorphic to the permutation representation of `G` on
`G ⧸ H →₀ (I →₀ R)` for a finite type `I`, hence free of finite rank on `H`-fixed vectors.

For subgroups `H ≤ S` of `G` with `H` open, pro-`p` and normal in `S`, and a smooth representation
`V` of `S` whose `H`-invariants are free over `R[S ⧸ H]` and finitely generated over `R` (for
instance when `V` satisfies `IsFreeLimit` for a family of open normal subgroups shrinking to the
identity), the compact induction `c-Ind_S^G` of the `H`-invariants of `V` is in
`HasProPFreeFixedBasis p`, and finite biproducts of such compact inductions are summands of finite
sums of representations in that class.

This is modelled on the proof of Proposition 4.10 of Harris, *Galois properties of cohomological
automorphic forms on GL(n)* (1999), printed pp.311-312: the terms `c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ)`
of (4.4.4) are rewritten by Frobenius reciprocity as (4.10.2), and there `C^j_m(ẽ)` is replaced by
its `H_p`-invariants, which are free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules. The compact induction of the
invariants is our construction; Harris's modules are not constructed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Induction

universe uR uG uV uM

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- For an open normal subgroup `H`, the representation of `G` on the `H`-invariants of a
representation `ρ` is smooth: every vector is fixed by the open subgroup `H`. -/
theorem isSmooth_invariantsInflation {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G)) :
    IsSmooth (invariantsInflation ρ H) := fun v =>
  ⟨⟨H, hH⟩, fun h => Subtype.ext (v.2 h)⟩

/-- The `H`-invariants of a smooth representation `V`, for an open normal subgroup `H`, as a
smooth representation of `G` (on which `G` acts through `G ⧸ H`). -/
abbrev smoothInvariantsInflation (V : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) : SmoothRep.{uR, uG, uV} R G :=
  SmoothRep.of (invariantsInflation V.representation H)
    (isSmooth_invariantsInflation V.representation H hH)

/-- The inclusion of the `H`-invariants into `V`, as a morphism of smooth representations. -/
def smoothInvariantsInflationι (V : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) : smoothInvariantsInflation V H hH ⟶ V :=
  SmoothRep.ofHom (V.representation.quotientToInvariants_lift H)

@[simp]
theorem smoothInvariantsInflationι_apply (V : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G)
    [H.Normal] (hH : IsOpen (H : Set G)) (v : smoothInvariantsInflation V H hH) :
    SmoothRep.hom (smoothInvariantsInflationι V H hH) v =
      (v : Representation.invariants (V.representation.comp H.subtype)).1 :=
  rfl

/-- The inclusion of the `H`-invariants into `V` is a monomorphism. -/
instance (V : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) : Mono (smoothInvariantsInflationι V H hH) := by
  refine ⟨fun {Z} f g hfg => ?_⟩
  ext v
  exact congrArg (fun T => SmoothRep.hom T v) hfg

variable [IsTopologicalGroup G]

/-- An equivalence of the `G ⧸ H`-representation on the `H`-invariants of `V` with the
permutation representation of `G ⧸ H` on itself with coefficients `M` gives an isomorphism of
smooth representations of `G` between the `H`-invariants and the permutation representation of
`G` on `G ⧸ H →₀ M`. -/
def smoothInvariantsInflationIso (V : SmoothRep.{uR, uG, max uG uM} R G) (H : Subgroup G)
    [H.Normal] (hH : IsOpen (H : Set G)) {M : Type (max uG uM)} [AddCommGroup M] [Module R M]
    (e : (V.representation.quotientToInvariants H).Equiv
      (permutation R (G ⧸ H) (G ⧸ H) M)) :
    smoothInvariantsInflation V H hH ≅ smoothPermutation R M H hH :=
  SmoothRep.mkIso ((Representation.Equiv.mk e.toLinearEquiv fun g =>
      e.toIntertwiningMap.isIntertwining' (QuotientGroup.mk' H g)).trans
    (permutationQuotientEquiv R H M))

end Smooth

section FiniteRank

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] {ρ : Representation R G V}

/-- If the `H`-invariants of `ρ` are a free `R[G ⧸ H]`-module in the sense of
`IsFreeOnInvariants` and are finitely generated as an `R`-module, then they are a free
`R[G ⧸ H]`-module of finite rank: the index type can be chosen finite. -/
theorem IsFreeOnInvariants.exists_finite {H : Subgroup G} [H.Normal]
    (h : IsFreeOnInvariants ρ R H)
    [Module.Finite R (Representation.invariants (ρ.comp H.subtype))] :
    ∃ I : Type uV, Finite I ∧ Nonempty ((ρ.quotientToInvariants H).Equiv
      (permutation R (G ⧸ H) (G ⧸ H) (I →₀ R))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (Representation.invariants (ρ.comp H.subtype))
    have := Module.subsingleton R (G ⧸ H →₀ PEmpty.{uV + 1} →₀ R)
    exact ⟨PEmpty, inferInstance, ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton _ _)
      fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩⟩
  · obtain ⟨I, ⟨e⟩⟩ := h
    refine ⟨I, ?_, ⟨e⟩⟩
    have : Module.Finite R (G ⧸ H →₀ I →₀ R) := Module.Finite.equiv e.toLinearEquiv
    have : Module.Finite R (I →₀ R) := Module.Finite.of_surjective
      (Finsupp.lapply (QuotientGroup.mk 1 : G ⧸ H))
      fun v => ⟨Finsupp.single _ v, Finsupp.single_eq_same⟩
    exact Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis I R (I →₀ R))

end FiniteRank

end Langlands.Induction

namespace Langlands.Cohomology

namespace HyperextScalarExtension

open Langlands.Induction

universe uR uG uV

section FreeInvariants

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- If the representation of `G ⧸ H` on the `H`-invariants of `V` is equivalent to the
permutation representation of `G ⧸ H` on itself with coefficients `I →₀ R` for a finite type `I`
(the free `R[G ⧸ H]`-module `⊕_I R[G ⧸ H]`), then the smooth representation of `G` on the
`H`-invariants of `V` is free of finite rank on `H`-fixed vectors. -/
theorem hasFreeFixedBasis_smoothInvariantsInflation
    (V : SmoothRep.{uR, uG, max uR uG uV} R G) (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) {I : Type (max uR uG uV)} [Finite I]
    (e : (V.representation.quotientToInvariants H).Equiv
      (permutation R (G ⧸ H) (G ⧸ H) (I →₀ R))) :
    HasFreeFixedBasis H (smoothInvariantsInflation V H hH) := by
  have := Fintype.ofFinite I
  let b : Module.Basis (Fin (Fintype.card I)) R (I →₀ R) :=
    (Finsupp.basisSingleOne).reindex (Fintype.equivFin I)
  exact HasFreeFixedBasis.of_iso (smoothInvariantsInflationIso.{uR, uG, max uR uV} V H hH e).symm
    ⟨_, _, isFreeOnFixedVectors_smoothPermutation.{uR, uG, max uR uV} H hH (I →₀ R) b⟩

/-- **Free invariants have free fixed bases.** If the `H`-invariants of `V`, for an open normal
subgroup `H`, are a free `R[G ⧸ H]`-module in the sense of `IsFreeOnInvariants` and are finitely
generated as an `R`-module, then they are free of finite rank on `H`-fixed vectors. -/
theorem _root_.Langlands.Induction.IsFreeOnInvariants.hasFreeFixedBasis
    {V : SmoothRep.{uR, uG, max uR uG uV} R G} {H : Subgroup G} [H.Normal]
    (hH : IsOpen (H : Set G)) (h : IsFreeOnInvariants V.representation R H)
    [Module.Finite R (Representation.invariants (V.representation.comp H.subtype))] :
    HasFreeFixedBasis H (smoothInvariantsInflation V H hH) := by
  obtain ⟨I, _, ⟨e⟩⟩ := h.exists_finite
  exact hasFreeFixedBasis_smoothInvariantsInflation V H hH e

/-- For an open normal pro-`p` subgroup `H`, if the `H`-invariants of `V` are a free
`R[G ⧸ H]`-module that is finitely generated as an `R`-module, then they are free of finite rank
on vectors fixed by a pro-`p` subgroup. -/
theorem _root_.Langlands.Induction.IsFreeOnInvariants.hasProPFreeFixedBasis {p : ℕ}
    {V : SmoothRep.{uR, uG, max uR uG uV} R G} {H : Subgroup G} [H.Normal]
    (hHp : IsProPSubgroup p H) (hH : IsOpen (H : Set G))
    (h : IsFreeOnInvariants V.representation R H)
    [Module.Finite R (Representation.invariants (V.representation.comp H.subtype))] :
    HasProPFreeFixedBasis p (smoothInvariantsInflation V H hH) :=
  ⟨H, hHp, h.hasFreeFixedBasis hH⟩

/-- **Compact induction of free invariants.** Let `H ≤ S` be subgroups of `G` with `H` open,
pro-`p` and normal in `S` (so `S` is open). If `V` is a smooth representation of `S` whose
`H`-invariants are a free `R[S ⧸ H]`-module (`IsFreeOnInvariants` for the subgroup
`H.subgroupOf S` of `S`) that is finitely generated as an `R`-module, then the compact induction
`c-Ind_S^G` of the `H`-invariants of `V` is free of finite rank on vectors fixed by a pro-`p`
subgroup. This is modelled on Harris 1999, proof of Proposition 4.10 (printed pp.311-312), where
`C^j_m(ẽ)` is replaced by its `H_p`-invariants in the Frobenius-reciprocity form (4.10.2) of the
terms `c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ)`; the compact induction of the invariants is ours. -/
theorem _root_.Langlands.Induction.IsFreeOnInvariants.hasProPFreeFixedBasis_smoothCompactInduction
    (S : Subgroup G) {p : ℕ} {H : Subgroup G} (hHp : IsProPSubgroup p H)
    (hH : IsOpen (H : Set G)) (hHS : H ≤ S) [(H.subgroupOf S).Normal]
    {V : SmoothRep.{uR, uG, max uR uG uV} R S}
    (h : IsFreeOnInvariants V.representation R (H.subgroupOf S))
    [Module.Finite R (Representation.invariants (V.representation.comp (H.subgroupOf S).subtype))] :
    HasProPFreeFixedBasis p ((Induction.smoothCompactInduction.{uR, uG, max uR uV} R S).obj
      (smoothInvariantsInflation V (H.subgroupOf S) (isOpen_subgroupOf hH S))) :=
  HasFreeFixedBasis.hasProPFreeFixedBasis_smoothCompactInduction.{uR, uG, max uR uV} S
    (Subgroup.isOpen_mono hHS hH) hHp hHS (h.hasFreeFixedBasis (isOpen_subgroupOf hH S))

/-- **Finite sums of compactly induced free invariants.** For a finite family of subgroups `S j`
of `G`, open pro-`p` subgroups `H j ≤ S j` of `G` normal in `S j`, and smooth representations
`V j` of `S j` whose `H j`-invariants are free `R[S j ⧸ H j]`-modules that are finitely generated
as `R`-modules, the biproduct of the compact inductions `c-Ind_{S j}^G` of the `H j`-invariants of
`V j` is a summand of a finite sum of representations free of finite rank on vectors fixed by
pro-`p` subgroups. The biproduct is modelled on the finite sums `⊕ c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ)`
that Harris's (4.4.4) gives in the proof of Proposition 4.10, with `C^j_m(ẽ)` replaced by its
`H_p`-invariants; Harris makes that replacement after Frobenius reciprocity, in (4.10.2) (Harris
1999, printed pp.310-312). -/
theorem isSummandOfFiniteSum_biproduct_compactInduction_invariants {J : Type} [Fintype J]
    (S : J → Subgroup G) {p : ℕ} {H : J → Subgroup G} (hHp : ∀ j, IsProPSubgroup p (H j))
    (hH : ∀ j, IsOpen (H j : Set G)) (hHS : ∀ j, H j ≤ S j)
    [∀ j, ((H j).subgroupOf (S j)).Normal] (V : ∀ j, SmoothRep.{uR, uG, max uR uG uV} R (S j))
    (h : ∀ j, IsFreeOnInvariants (V j).representation R ((H j).subgroupOf (S j)))
    [∀ j, Module.Finite R (Representation.invariants
      ((V j).representation.comp ((H j).subgroupOf (S j)).subtype))]
    [HasBiproduct fun j => (Induction.smoothCompactInduction.{uR, uG, max uR uV} R (S j)).obj
      (smoothInvariantsInflation (V j) ((H j).subgroupOf (S j))
        (isOpen_subgroupOf (hH j) (S j)))] :
    IsSummandOfFiniteSum (HasProPFreeFixedBasis p)
      (⨁ fun j => (Induction.smoothCompactInduction.{uR, uG, max uR uV} R (S j)).obj
        (smoothInvariantsInflation (V j) ((H j).subgroupOf (S j))
          (isOpen_subgroupOf (hH j) (S j)))) :=
  IsSummandOfFiniteSum.biproduct _ fun j => IsSummandOfFiniteSum.of_prop
    ((h j).hasProPFreeFixedBasis_smoothCompactInduction (S j) (hHp j) (hH j) (hHS j))

omit [IsTopologicalGroup G] in
/-- For subgroups `H ≤ S` with `H` compact, the subgroup `H.subgroupOf S` of `S` is compact. -/
theorem isCompact_subgroupOf {H S : Subgroup G} (hHc : IsCompact (H : Set G)) (hHS : H ≤ S) :
    IsCompact ((H.subgroupOf S : Subgroup S) : Set S) := by
  rw [Subgroup.coe_subgroupOf]
  exact (Topology.IsInducing.subtypeVal (t := (S : Set G))).isCompact_preimage' hHc
    fun x hx => ⟨⟨x, hHS hx⟩, rfl⟩

end FreeInvariants

section FreeLimit

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type*}

/-- **Direct limits of free modules: compact induction of pro-`p` invariants.** Let `S` be a
subgroup of `G` and `V` a smooth representation of `S` that is a direct limit of free
`R[S ⧸ K i]`-modules (`IsFreeLimit`) for a family `K` of open normal subgroups of `S` shrinking to
the identity. Let `H ≤ S` be an open pro-`p` subgroup of `G` that is normal in `S`, with
`H`-invariants of `V` finitely generated as an `R`-module. Then the compact induction `c-Ind_S^G`
of the `H`-invariants of `V` is free of finite rank on vectors fixed by a pro-`p` subgroup. This is
modelled on Harris 1999, proof of Proposition 4.10 (printed pp.311-312), where `C^j(ẽ)` is a
direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules and `C^j_m(ẽ)` is replaced by its
`H_p`-invariants in (4.10.2); the compact induction of the invariants is ours. -/
theorem _root_.Langlands.Induction.IsFreeLimit.hasProPFreeFixedBasis_smoothCompactInduction
    (S : Subgroup G) {V : SmoothRep.{uR, uG, max uR uG uV} R S} {K : ι → Subgroup S}
    [∀ i, (K i).Normal] (hV : IsFreeLimit V.representation R K)
    (hKo : ∀ i, IsOpen (K i : Set S)) (hshrink : ∀ U ∈ nhds (1 : S), ∃ i, (K i : Set S) ⊆ U)
    {p : ℕ} {H : Subgroup G} (hHp : IsProPSubgroup p H) (hH : IsOpen (H : Set G)) (hHS : H ≤ S)
    [(H.subgroupOf S).Normal]
    [Module.Finite R (Representation.invariants (V.representation.comp (H.subgroupOf S).subtype))] :
    HasProPFreeFixedBasis p ((Induction.smoothCompactInduction.{uR, uG, max uR uV} R S).obj
      (smoothInvariantsInflation V (H.subgroupOf S) (isOpen_subgroupOf hH S))) :=
  (hV.isFreeOnInvariants_of_isOpen hKo hshrink (H.subgroupOf S) (isOpen_subgroupOf hH S)
    (isCompact_subgroupOf (isCompact_iff_compactSpace.mpr hHp.compactSpace) hHS)
    ).hasProPFreeFixedBasis_smoothCompactInduction S hHp hH hHS

/-- **Finite sums of compactly induced pro-`p` invariants of direct limits of free modules.** For
a finite family of subgroups `S j` of `G` and smooth representations `V j` of `S j` that are
direct limits of free modules for families `K j` of open normal subgroups of `S j` shrinking to
the identity, and open pro-`p` subgroups `H j ≤ S j` of `G` normal in `S j` with `H j`-invariants
of `V j` finitely generated as `R`-modules, the biproduct of the compact inductions
`c-Ind_{S j}^G` of the `H j`-invariants of `V j` is a summand of a finite sum of representations
free of finite rank on vectors fixed by pro-`p` subgroups. As for
`isSummandOfFiniteSum_biproduct_compactInduction_invariants`, this is modelled on Harris's (4.4.4)
with `C^j_m(ẽ)` replaced by its `H_p`-invariants, a replacement Harris makes in (4.10.2)
(Harris 1999, printed pp.310-312). -/
theorem isSummandOfFiniteSum_biproduct_compactInduction_isFreeLimit {J : Type} [Fintype J]
    (S : J → Subgroup G) (V : ∀ j, SmoothRep.{uR, uG, max uR uG uV} R (S j))
    {K : ∀ j, ι → Subgroup (S j)} [∀ j i, (K j i).Normal]
    (hV : ∀ j, IsFreeLimit (V j).representation R (K j))
    (hKo : ∀ j i, IsOpen (K j i : Set (S j)))
    (hshrink : ∀ j, ∀ U ∈ nhds (1 : S j), ∃ i, (K j i : Set (S j)) ⊆ U)
    {p : ℕ} {H : J → Subgroup G} (hHp : ∀ j, IsProPSubgroup p (H j))
    (hH : ∀ j, IsOpen (H j : Set G)) (hHS : ∀ j, H j ≤ S j)
    [∀ j, ((H j).subgroupOf (S j)).Normal]
    [∀ j, Module.Finite R (Representation.invariants
      ((V j).representation.comp ((H j).subgroupOf (S j)).subtype))]
    [HasBiproduct fun j => (Induction.smoothCompactInduction.{uR, uG, max uR uV} R (S j)).obj
      (smoothInvariantsInflation (V j) ((H j).subgroupOf (S j))
        (isOpen_subgroupOf (hH j) (S j)))] :
    IsSummandOfFiniteSum (HasProPFreeFixedBasis p)
      (⨁ fun j => (Induction.smoothCompactInduction.{uR, uG, max uR uV} R (S j)).obj
        (smoothInvariantsInflation (V j) ((H j).subgroupOf (S j))
          (isOpen_subgroupOf (hH j) (S j)))) :=
  IsSummandOfFiniteSum.biproduct _ fun j => IsSummandOfFiniteSum.of_prop
    ((hV j).hasProPFreeFixedBasis_smoothCompactInduction (S j) (hKo j) (hshrink j) (hHp j) (hH j)
      (hHS j))

end FreeLimit

end HyperextScalarExtension

end Langlands.Cohomology
