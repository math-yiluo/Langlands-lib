import Langlands.Cohomology.DivisibleSystem.TotalComparison
import Langlands.Cohomology.ProPInvariants.Statement
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# Pro-`p` invariants of `ℓ`-divisible systems

Harris 1999, §2, p.305, takes an open normal pro-`p` subgroup `H` of `S(ẽ)`, `p ≠ ℓ`, and uses
that `H⁰(H, ·)` is exact on `ℓ`-primary torsion modules. The Invariants, InvariantTotal and
TotalComparison modules keep the resulting surjectivity on `H`-invariants as an explicit
hypothesis `hK`. This module derives that hypothesis from `ProPInvariantsExactStatement`
(exactness of invariants of a pro-`p` group on smooth representations with `p` invertible in
the coefficients), which is taken as a hypothesis `hP` and is not proved here.

It defines pro-`p` subgroups of a topological group, shows that the `H`-invariants of an
epimorphism of smooth representations of `G` are an epimorphism when `H` is pro-`p` and `p` is
invertible in `R`, and specializes the systems of the three modules above, for general
`ℓ`-divisible systems of complexes and for the compact sections of the truncated smooth
Godement resolutions, to this case.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w uR uG uV u

section ProP

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A subgroup `H` of a topological group is pro-`p` if, with the subspace topology, it is
compact and totally disconnected and its quotient by every open normal subgroup is a
`p`-group. These are the hypotheses on `H` of `ProPInvariantsExactStatement`. -/
structure IsProPSubgroup (p : ℕ) (H : Subgroup G) : Prop where
  prime : p.Prime
  compactSpace : CompactSpace H
  totallyDisconnectedSpace : TotallyDisconnectedSpace H
  isPGroup : ∀ N : OpenNormalSubgroup H, IsPGroup p (H ⧸ N.toSubgroup)

variable (R : Type uR) [CommRing R]

/-- The restriction of a smooth representation of `G` to a subgroup `H` is smooth for the
subspace topology on `H`. -/
lemma isSmooth_res_subtype (H : Subgroup G) (A : SmoothRep.{uR, uG, uV} R G) :
    IsSmooth ((Rep.resFunctor H.subtype).obj (SmoothRep.toRep.obj A)).ρ :=
  isSmooth_comp H.subtype continuous_subtype_val A.property

variable {R} [IsTopologicalGroup G]

/-- Given `ProPInvariantsExactStatement`, the `H`-invariants of an epimorphism of smooth
representations of `G` are an epimorphism, for a normal pro-`p` subgroup `H` of `G` and `p`
invertible in `R`. -/
theorem epi_smoothQuotientInvariants_map (hP : ProPInvariantsExactStatement.{uG, uR, uV})
    {p : ℕ} {H : Subgroup G} [H.Normal] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) [Epi f] :
    Epi ((smoothQuotientInvariants R H).map f) := by
  have := hH.compactSpace
  have := hH.totallyDisconnectedSpace
  have : (SmoothRep.toRep : SmoothRep.{uR, uG, uV} R G ⥤ _).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel f) }
  have hS' : ((S.map SmoothRep.toRep).map (Rep.resFunctor H.subtype)).ShortExact :=
    (Rep.shortExact_res H.subtype).2 (hS.map SmoothRep.toRep)
  have h := (hP p hH.prime H hH.isPGroup R hR _ hS' (isSmooth_res_subtype R H _)
    (isSmooth_res_subtype R H _) (isSmooth_res_subtype R H _)).epi_g
  rw [Rep.epi_iff_surjective]
  exact (ModuleCat.epi_iff_surjective _).1 h

/-- Given `ProPInvariantsExactStatement`, the `H`-invariants of a functor to smooth
representations keep its epimorphisms, for a normal pro-`p` subgroup `H` of `G` and `p`
invertible in `R`. -/
lemma epi_comp_smoothQuotientInvariants_map (hP : ProPInvariantsExactStatement.{uG, uR, uV})
    {p : ℕ} {H : Subgroup G} [H.Normal] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
    {C : Type*} [Category C] (Φ : C ⥤ SmoothRep.{uR, uG, uV} R G) {Y Z : C} (f : Y ⟶ Z)
    (hf : Epi (Φ.map f)) : Epi ((Φ ⋙ smoothQuotientInvariants R H).map f) :=
  epi_smoothQuotientInvariants_map hP hH hR (Φ.map f)

end ProP

namespace DivisibleSystem

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ℓ : ℕ} (hP : ProPInvariantsExactStatement.{uG, uR, uV}) {p : ℕ}
  {H : Subgroup G} [H.Normal] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ)

include hP hH hR in
/-- Given `ProPInvariantsExactStatement`, every degree of every projection of a system of
complexes of smooth representations stays an epimorphism on `H`-invariants, for a normal
pro-`p` subgroup `H` and `p` invertible in `R`: the hypothesis `hK` of the Invariants
module. -/
lemma epi_smoothQuotientInvariants_map_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)) :=
  have := K.epi_projection_f h q
  epi_smoothQuotientInvariants_map hP hH hR _

/-- The `H`-invariants system `quotientInvariantsComplexes` for a normal pro-`p` subgroup `H`
and `p` invertible in `R`, given `ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsComplexes :
    DivisibleSystem (CochainComplex (Rep.{uV} R (G ⧸ H)) ℕ) ℓ :=
  K.quotientInvariantsComplexes H (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR)

/-- The inclusion `quotientInvariantsComplexesInclusion` of the inflated `H`-invariants for a
normal pro-`p` subgroup `H` and `p` invertible in `R`, given
`ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsComplexesInclusion :
    K.inflatedQuotientInvariantsComplexes H
        (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR) ⟶
      K.toRepComplexes :=
  K.quotientInvariantsComplexesInclusion H
    (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR)

end Smooth

section SmoothTotal

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ℓ : ℕ} (N : ℕ)
  (hP : ProPInvariantsExactStatement.{uG, uR, max w uR uG}) {p : ℕ}
  {H : Subgroup G} [H.Normal] [H.FiniteIndex] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)

/-- Harris's `C_m^{•,H}` (`quotientInvariantsTotalSystem`, rows `q < N`) for a normal pro-`p`
subgroup `H` of finite index and `p` invertible in `R`, given
`ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsTotalSystem :
    DivisibleSystem (CochainComplex (Rep.{max w uR uG} R (G ⧸ H)) ℤ) ℓ :=
  K.quotientInvariantsTotalSystem N H (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR)

/-- The totalized augmentation `quotientInvariantsTotalSystemAugmentation` for a normal pro-`p`
subgroup `H` of finite index and `p` invertible in `R`, given
`ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsTotalSystemAugmentation :
    K.proPQuotientInvariantsTotalSystem N hP hH hR ⟶
      ((K.proPQuotientInvariantsComplexes hP hH hR).map
        ((ChainComplex.single₀ (Rep.{max w uR uG} R (G ⧸ H))).mapHomologicalComplex
          (ComplexShape.up ℕ))).totalSystem N :=
  K.quotientInvariantsTotalSystemAugmentation N H
    (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR)

/-- The morphism `quotientInvariantsTotalSystemToExtend` from Harris's `C_m^{•,H}` to the
`H`-invariants system extended to `ℤ`, for `K` vanishing in degrees `q ≥ N`, a normal pro-`p`
subgroup `H` of finite index and `p` invertible in `R`, given
`ProPInvariantsExactStatement`. -/
abbrev proPQuotientInvariantsTotalSystemToExtend
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    K.proPQuotientInvariantsTotalSystem N hP hH hR ⟶
      (K.proPQuotientInvariantsComplexes hP hH hR).extendSystem :=
  K.quotientInvariantsTotalSystemToExtend N H
    (K.epi_smoothQuotientInvariants_map_projection_f hP hH hR) hN

end SmoothTotal

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (hP : ProPInvariantsExactStatement.{u, u, u}) {p : ℕ} {H : Subgroup G} [H.Normal]
  (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Harris's system `{G_m(U)^H}` (`smoothGodementTruncatedQuotientInvariantSectionsSystem`) for a
normal pro-`p` subgroup `H` and `p` invertible in `R`, given `ProPInvariantsExactStatement`
and the compact-section hypotheses of `smoothGodementTruncatedCompactSectionsSystem`. -/
abbrev proPSmoothGodementTruncatedQuotientInvariantSectionsSystem :
    DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℕ) ℓ :=
  smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H
    (fun q hq _ _ hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hterm q hq hm))
    (fun hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hres hm))

variable [H.FiniteIndex]

/-- Harris's `C_m^{•,H}` (`smoothGodementInvariantTotalSystem`, rows `q < D + 2`) for a normal
pro-`p` subgroup `H` of finite index and `p` invertible in `R`, given
`ProPInvariantsExactStatement` and the compact-section hypotheses of
`smoothGodementTruncatedCompactSectionsSystem`. -/
abbrev proPSmoothGodementInvariantTotalSystem :
    DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ :=
  smoothGodementInvariantTotalSystem h T D H
    (fun q hq _ _ hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hterm q hq hm))
    (fun hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hres hm))

/-- The morphism `smoothGodementInvariantTotalSystemToExtend` from Harris's `C_m^{•,H}` to the
`H`-invariant section complexes extended to `ℤ`, for a normal pro-`p` subgroup `H` of finite
index and `p` invertible in `R`, given `ProPInvariantsExactStatement` and the compact-section
hypotheses of `smoothGodementTruncatedCompactSectionsSystem`. -/
abbrev proPSmoothGodementInvariantTotalSystemToExtend :
    proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres ⟶
      (proPSmoothGodementTruncatedQuotientInvariantSectionsSystem h T D hP hH hR hterm
        hres).extendSystem :=
  smoothGodementInvariantTotalSystemToExtend h T D H
    (fun q hq _ _ hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hterm q hq hm))
    (fun hm => epi_comp_smoothQuotientInvariants_map hP hH hR _ _ (hres hm))

end SmoothGodement

end DivisibleSystem

end Langlands.Cohomology
