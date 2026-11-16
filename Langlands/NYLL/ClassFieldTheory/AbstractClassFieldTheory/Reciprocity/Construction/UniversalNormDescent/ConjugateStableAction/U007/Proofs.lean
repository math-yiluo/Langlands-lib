/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation.SubgroupEquiv.Definitions

/-!
# NYLL M043.007: relative norms commute with the conjugation-stable action

Modified by Worker 739, 16 November 2026: prove the published target
`relativeNorm_conjugateStableActionStatement` (M043.007) by the source proof
of `relativeNorm_conjugateStableAction` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof with `show` stating it unfolded. Port as private
declarations of this module, with their source statements, the source
helpers it uses: from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`
the theorems `conjugateClosedSubgroup_mono` (M035.001),
`map_extensionSubgroup_conjugate` (M035.004),
`relativeConjugateCosetEquiv_mk` (M035.006), `finite_conjugateExtension`
(M035.010), `relativeCosetAction_conjugate` (source-private) and
`relativeNorm_conjugate_apply` (M035.012) and the definition
`relativeConjugateCosetEquiv` (M035.005), and from the source file of the
target the private theorems `transport_fixed_coe` (M043.004) and
`relativeNorm_transport_coe` (M043.005). Replace each source
`rw [conjugateClosedSubgroup_mem]` by an application of the published
theorem's `.1`/`.2`; in `map_extensionSubgroup_conjugate` replace the
following `simpa [mul_assoc] using hk`, which here leaves `hk` as membership
in `extensionSubgroup K L hLK`, by a rewrite with
`s * (s⁻¹ * k.1 * s) * s⁻¹ = k.1` (by `simp [mul_assoc]`) and `hk` read as
`↑k ∈ L.toSubgroup`. Replace the source rewrites with `relativeCosetAction_mk` and
`conjugateFixedElement_coe` by a `change` to the reduced goal, and the source
`simp only [relativeNorm_apply_coe, relativeNormValue,
conjugateFixedElement_coe]` by a `change` to the defining sums, because these
lemmas are published with `...Statement` types or are not in the Library.
Replace the source imports by the published statement module and the module
of the published M035.002 definition `conjugateSubgroupEquiv`, and omit the
`@[simp]` attributes, the docstrings of the private ports, the unused
universes and opens and the rest of both source files. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

private theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  refine (conjugateClosedSubgroup_mem K s x).2 ?_
  exact hLK ((conjugateClosedSubgroup_mem L s x).1 hx)

private theorem map_extensionSubgroup_conjugate [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (extensionSubgroup K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    refine (conjugateClosedSubgroup_mem L s _).2 ?_
    have hk' : (k : G) ∈ L.toSubgroup := hk
    have he : s * (s⁻¹ * k.1 * s) * s⁻¹ = k.1 := by simp [mul_assoc]
    rw [he]
    exact hk'
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · change s * x.1 * s⁻¹ ∈ L.toSubgroup
      exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · exact (conjugateSubgroupEquiv K s).apply_symm_apply x

private noncomputable def relativeConjugateCosetEquiv [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := extensionSubgroup K L hLK
    let Hs := extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
    have hmap : H.map e.toMonoidHom = Hs :=
      map_extensionSubgroup_conjugate K L hLK s
    change x⁻¹ * y ∈ H ↔ (e x)⁻¹ * e y ∈ Hs
    rw [← hmap]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      change e (x⁻¹ * y) = (e x)⁻¹ * e y
      rw [map_mul, map_inv]
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        change e z = (e x)⁻¹ * e y at hez
        simpa only [map_mul, map_inv] using hez
      rw [← heq]
      exact hz)

private theorem relativeConjugateCosetEquiv_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

private theorem finite_conjugateExtension [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (relativeConjugateCosetEquiv K L hLK s)

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

private theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L hLK s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeConjugateCosetEquiv_mk]
  change A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) = A.ρ s⁻¹ (A.ρ k.1 a.1)
  calc
    A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) =
        A.ρ ((s⁻¹ * k.1 * s) * s⁻¹) a.1 := by
      have hm := congrArg (fun φ => φ a.1)
        (map_mul A.ρ (s⁻¹ * k.1 * s) s⁻¹)
      exact hm.symm
    _ = A.ρ (s⁻¹ * k.1) a.1 := by
      congr 2
      simp [mul_assoc]
    _ = A.ρ s⁻¹ (A.ρ k.1 a.1) := by
      exact congrArg (fun φ => φ a.1) (map_mul A.ρ s⁻¹ k.1)

private theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e := relativeConjugateCosetEquiv K L hLK s
  let conjugateFintype : Fintype
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) :=
    Fintype.ofEquiv (K.toSubgroup ⧸ extensionSubgroup K L hLK) e
  have hconjugateFintype : Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) = conjugateFintype :=
    Subsingleton.elim _ _
  apply Subtype.ext
  change
    (letI := Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj)
     ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q) =
      A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q)
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := by
          exact (e.sum_comp fun q =>
            relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a) q).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact relativeCosetAction_conjugate A K L hLK s a q
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]

end Representation

private theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

private theorem relativeNorm_transport_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ extensionSubgroup F' E' hE'F')]
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) : B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') : B.V) := by
  cases hF
  cases hE
  rfl

/-- Relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
theorem relativeNorm_conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm_conjugateStableActionStatement B F E hEF s hF hE a := by
  show relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
    conjugateStableAction B F s hF (relativeNorm B F E hEF a)
  let hConj := conjugateClosedSubgroup_mono hEF s
  let : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup F s)
        (conjugateClosedSubgroup E s) hConj) :=
    finite_conjugateExtension F E hEF s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a) :
        ambientFixedAddSubgroup B F) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a) :
            ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := by
      exact relativeNorm_transport_coe B
        (conjugateClosedSubgroup F s) (conjugateClosedSubgroup E s) F E
        hF hE hConj hEF (conjugateFixedElement B E s a)
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B F) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm

end

end Langlands.NYLL.ClassFormation
