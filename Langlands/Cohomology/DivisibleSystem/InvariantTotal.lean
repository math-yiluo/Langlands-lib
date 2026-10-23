import Langlands.Cohomology.DivisibleSystem.Invariants
import Langlands.Cohomology.DivisibleSystem.Total

/-!
# Harris's complexes `C_m^{•,H}`

Harris 1999, §2, p.306, lets `C_m^{•,H}` be the simple complex of the double complex
`K_m^{-•,•,H}` of standard resolutions (2.5) of the `H`-invariants `M_m^{•,H}` of the section
complexes, for `H` normal in `S(ẽ)` with `S(ẽ)/H` finite. This module applies the total
complexes of the Total module, for the finite group `Γ = G ⧸ H`, to the `H`-invariants systems
of the Invariants module.

`H` is a normal subgroup of finite index, so `G ⧸ H` is finite (Mathlib's
`Subgroup.finite_quotient_of_finiteIndex`). The rows are restricted to `q < N`; for the
truncated smooth Godement systems, which vanish above degree `D + 1`, the module takes
`N = D + 2`. Total degrees and signs are those of the Total module. No freeness, no
quasi-isomorphism and no comparison between different `H` is proved.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w uR uG u

namespace DivisibleSystem

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- The total complexes, rows restricted to `q < N`, of the standard resolutions along
`Ind_1^Γ Res_1^Γ`, `Γ = G ⧸ H`, of the `H`-invariants of an `ℓ`-divisible system of complexes of
smooth representations, given that every degree of every projection stays an epimorphism on
`H`-invariants (Harris's `C_m^{•,H}` of p.306 for a general system `K`). -/
abbrev quotientInvariantsTotalSystem
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    DivisibleSystem (CochainComplex (Rep.{max w uR uG} R (G ⧸ H)) ℤ) ℓ :=
  (K.quotientInvariantsComplexes H hK).groupStandardTotalSystem N

/-- The totalized augmentation of `quotientInvariantsTotalSystem`. Its target is the total
complex (rows `q < N`) of the `H`-invariants system placed in resolution degree `0`. -/
abbrev quotientInvariantsTotalSystemAugmentation
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    K.quotientInvariantsTotalSystem N H hK ⟶
      ((K.quotientInvariantsComplexes H hK).map
        ((ChainComplex.single₀ (Rep.{max w uR uG} R (G ⧸ H))).mapHomologicalComplex
          (ComplexShape.up ℕ))).totalSystem N :=
  (K.quotientInvariantsComplexes H hK).groupStandardTotalSystemAugmentation N

/-- `quotientInvariantsTotalSystem` vanishes in degrees `n ≥ N`. -/
lemma isZero_quotientInvariantsTotalSystem_obj_X
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (m : ℕ) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    IsZero (((K.quotientInvariantsTotalSystem N H hK).obj m).X n) :=
  isZero_totalSystem_obj_X N _ m hn

end Smooth

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal]

/-- The `H`-invariant truncated section complexes vanish in degrees `q ≥ D + 2`, so the rows
`q < D + 2` are all the rows that can be nonzero. -/
lemma isZero_smoothGodementTruncatedQuotientInvariantSectionsSystem_obj_X
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (m : ℕ) {q : ℕ} (hq : D + 2 ≤ q) :
    IsZero (((smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres).obj
      m).X q) :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  isZero_truncatedResolutionSectionsSystem_obj_X (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T D (smoothSheafCompactSections R G X ⋙
      smoothQuotientInvariants R H) hterm hres m (by omega)

variable [H.FiniteIndex]

/-- Harris's `C_m^{•,H}` (p.306): the total complexes, rows `q < D + 2`, of the standard
resolutions along `Ind_1^Γ Res_1^Γ`, `Γ = G ⧸ H`, of the `H`-invariants of the compact sections
of the truncated smooth Godement resolutions, under the hypotheses of
`smoothGodementTruncatedQuotientInvariantSectionsSystem`. -/
abbrev smoothGodementInvariantTotalSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ :=
  groupStandardTotalSystem.{0} (D + 2)
    (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres)

/-- The totalized augmentation of `smoothGodementInvariantTotalSystem`. Its target is the total
complex (rows `q < D + 2`) of the `H`-invariant section complexes placed in resolution
degree `0`. -/
abbrev smoothGodementInvariantTotalSystemAugmentation
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementInvariantTotalSystem h T D H hterm hres ⟶
      ((smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres).map
        ((ChainComplex.single₀ (Rep.{u} R (G ⧸ H))).mapHomologicalComplex
          (ComplexShape.up ℕ))).totalSystem (D + 2) :=
  groupStandardTotalSystemAugmentation.{0} (D + 2)
    (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres)

/-- `smoothGodementInvariantTotalSystem` vanishes in degrees `n ≥ D + 2`. -/
lemma isZero_smoothGodementInvariantTotalSystem_obj_X
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (m : ℕ) {n : ℤ} (hn : ((D + 2 : ℕ) : ℤ) ≤ n) :
    IsZero (((smoothGodementInvariantTotalSystem h T D H hterm hres).obj m).X n) :=
  isZero_totalSystem_obj_X (D + 2) _ m hn

end SmoothGodement

end DivisibleSystem

end Langlands.Cohomology
