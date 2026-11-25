/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
public import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-!
# Finiteness of the cohomology of coherent sheaves on projective schemes

The cohomology groups of a coherent sheaf on a closed subscheme of `ℙᵈ_k` are finite-dimensional
`k`-vector spaces (Serre; Hartshorne III.5.2). The proof is by descending induction on the degree,
for all coherent sheaves on `ℙᵈ_k` at once: the cohomology vanishes above `d`
(`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_of_lt`), a coherent sheaf is a quotient of a
finite sum of twists `𝒪(-m)` with coherent kernel
(`AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist`), and the cohomology of the twists is
finite-dimensional. A closed subscheme reduces to `ℙᵈ_k` by pushing forward.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.finiteDimensional_H_twist`: `H^q(ℙᵈ_k, 𝒪(m))` is
  finite-dimensional.
- `AlgebraicGeometry.ProjectiveSpace.finiteDimensional_H`: the cohomology of a coherent sheaf on
  `ℙᵈ_k` is finite-dimensional.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- In an exact sequence `M ⟶ N ⟶ P` of modules over a noetherian ring, `N` is finite when `M`
and `P` are. -/
lemma Module.Finite.of_exact_of_isNoetherianRing {R M N P : Type*} [CommRing R]
    [IsNoetherianRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    [Module.Finite R M] [Module.Finite R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) : Module.Finite R N := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, LinearMap.exact_iff.1 h, LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map f

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- `H^q(M)` is finite-dimensional when `M` is isomorphic to a module with finite-dimensional
`H^q`. -/
lemma finiteDimensional_H_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    [FiniteDimensional k (M.H q)] : FiniteDimensional k (N.H q) :=
  Module.Finite.equiv
    { H.mapLinearEquiv e q with
      map_smul' := fun c x ↦ (H.mapLinearEquiv e q).map_smul (globalSectionsRingHom k c) x }

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`, `H^q(M₃)` is finite-dimensional when
`H^q(M₂)` and `H^{q+1}(M₁)` are. -/
lemma finiteDimensional_H_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    [FiniteDimensional k (S.X₂.H q)] [FiniteDimensional k (S.X₁.H (q + 1))] :
    FiniteDimensional k (S.X₃.H q) :=
  Module.Finite.of_exact_of_isNoetherianRing (f := H.mapLinearMap k S.g q)
    (g := H.δLinearMap k hS q) fun x ↦ by
    change H.δ hS q x = 0 ↔ x ∈ Set.range (H.map S.g q)
    rw [← AddMonoidHom.mem_ker, H.ker_δ_eq_range_map_g hS q]
    rfl

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Cohomology of a finite coproduct.** If every `H^q(G i)` is finite-dimensional, so is
`H^q(∐ G)`. -/
lemma finiteDimensional_H_sigma {ι : Type*} [Finite ι] (G : ι → X.Modules) (q : ℕ)
    [∀ i, FiniteDimensional k ((G i).H q)] : FiniteDimensional k ((∐ G).H q) := by
  classical
  -- reindex by `Fin r`, since the biproduct API is stated for index types in `Type`
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  suffices ∀ G' : Fin r → X.Modules, (∀ i, FiniteDimensional k ((G' i).H q)) →
      FiniteDimensional k ((∐ G').H q) by
    have := this (G ∘ e.symm) fun i ↦ inferInstanceAs (FiniteDimensional k ((G (e.symm i)).H q))
    exact finiteDimensional_H_of_iso k (Sigma.reindex e.symm G) q
  intro G _
  have : FiniteDimensional k ((⨁ G).H q) :=
    Module.Finite.equiv (H.isBilimitLinearEquiv k (biproduct.isBilimit G) q).symm
  exact finiteDimensional_H_of_iso k (biproduct.isoCoproduct G) q

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u}

/-- With a single homogeneous coordinate, the Laurent monomials of degree `m` reduce to `x^m`,
so the monomial Čech cochains are finite. -/
lemma finite_monomialCechSupport [Fintype n] [Subsingleton n] (m : ℤ) {p : ℕ}
    (σ : Fin (p + 1) → n) : (monomialCechSupport n m σ).Finite := by
  refine Set.Subsingleton.finite fun e he e' he' ↦ funext fun i ↦ ?_
  have h₁ := he.1
  have h₂ := he'.1
  rw [Finset.sum_eq_single i (fun j _ hj ↦ absurd (Subsingleton.elim j i) hj) (by simp)] at h₁ h₂
  rw [h₁, h₂]

variable (k : Type u) [Field k]

/-- **The cohomology of the twisting sheaves is finite-dimensional.** `H^q(ℙᵈ_k, 𝒪(m))` is a
finite-dimensional `k`-vector space for all `q` and `m`, by the computation of these groups
(`nonempty_H_zero_twist_equiv`, `subsingleton_H_twist_of_ne`, `subsingleton_H_twist_top`,
`nonempty_H_twist_top_equiv_dual`). -/
theorem finiteDimensional_H_twist [Finite n] (m : ℤ) (q : ℕ) :
    FiniteDimensional k ((ProjectiveSpace.twist n (Spec (.of k)) m).H q) := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · have := ProjectiveSpace.subsingleton_H_of_isEmpty (Spec (.of k))
      (ProjectiveSpace.twist n (Spec (.of k)) m) q
    infer_instance
  have := Fintype.ofFinite n
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rcases subsingleton_or_nontrivial n with hsub | hnt
    · -- a single coordinate: the monomial Čech cochains are finite
      obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m 0
      suffices FiniteDimensional k ((monomialCechComplex n k m).homology 0) from
        Module.Finite.equiv e.symm
      have (σ : Fin 1 → n) : Module.Finite k (Finsupp.supported k k (monomialCechSupport n m σ)) :=
        have := (finite_monomialCechSupport m σ).to_subtype
        Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm
      have : Module.Finite k ((monomialCechComplex n k m).X 0) :=
        inferInstanceAs (Module.Finite k (MonomialCechCochain n k m 0))
      have : Module.Finite k (LinearMap.ker ((monomialCechComplex n k m).d 0 1).hom) :=
        Module.Finite.of_injective (LinearMap.ker _).subtype (LinearMap.ker _).injective_subtype
      exact Module.Finite.equiv (monomialCechComplex n k m).homologyZeroLinearEquiv.symm
    · rcases le_or_gt 0 m with hm | hm
      · lift m to ℕ using hm
        obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_zero_twist_equiv n k D hD m
        have := (Finsupp.finite_of_degree_eq (σ := n) m).to_subtype
        have : Module.Finite k (MvPolynomial.homogeneousSubmodule n k m) :=
          Module.Finite.of_basis (homogeneousSubmoduleBasis n k m)
        exact Module.Finite.equiv e.symm
      · obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_linearEquiv_homology n k m 0
        have := subsingleton_monomialCechComplex_homology_zero n k hm
        have : Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H 0) :=
          e.toEquiv.subsingleton
        infer_instance
  by_cases hqD : q = D
  · subst hqD
    rcases le_or_gt (-(q : ℤ)) m with hm | hm
    · have := ProjectiveSpace.subsingleton_H_twist_top n k q hq.ne' hD m hm
      infer_instance
    · obtain ⟨e⟩ := ProjectiveSpace.nonempty_H_twist_top_equiv_dual n k q hD m (by omega)
      have := (Finsupp.finite_of_degree_eq (σ := n) (-m - q - 1).toNat).to_subtype
      have : Module.Finite k (MvPolynomial.homogeneousSubmodule n k (-m - q - 1).toNat) :=
        Module.Finite.of_basis (homogeneousSubmoduleBasis n k _)
      exact Module.Finite.equiv e.symm
  · have := ProjectiveSpace.subsingleton_H_twist_of_ne n k D hD q m hq.ne' hqD
    infer_instance

/-- **The cohomology of a coherent sheaf on `ℙᵈ_k` is finite-dimensional** (Hartshorne III.5.2).

By descending induction on the degree, for all coherent sheaves at once: the cohomology vanishes
above `d` (`AlgebraicGeometry.ProjectiveSpace.subsingleton_H_of_lt`). A coherent `𝒢` sits in
`0 ⟶ 𝒦 ⟶ ⨁ⱼ 𝒪(-mⱼ) ⟶ 𝒢 ⟶ 0` with `𝒦` coherent
(`AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist`), so `H^q(𝒢)` sits between the
finite-dimensional `⨁ⱼ H^q(𝒪(-mⱼ))` and `H^{q+1}(𝒦)`, finite-dimensional by induction. -/
theorem finiteDimensional_H [Finite n] (ℱ : (ℙ(n; Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have := ProjectiveSpace.subsingleton_H_of_isEmpty _ ℱ q
    infer_instance
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.card n = D + 1 :=
    ⟨Nat.card n - 1, by have := Nat.card_pos (α := n); omega⟩
  suffices key : ∀ j : ℕ, ∀ (𝒢 : (ℙ(n; Spec (.of k))).Modules)
      [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢]
      [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of k))).ringCatSheaf) 𝒢],
      ∀ q, D < q + j → FiniteDimensional k (𝒢.H q) from key (D + 1) ℱ q (by omega)
  intro j
  induction j with
  | zero =>
    intro 𝒢 _ _ q hq
    have := ProjectiveSpace.subsingleton_H_of_lt n k hD 𝒢 (q := q) (by omega)
    infer_instance
  | succ j ih =>
    intro 𝒢 _ _ q hq
    obtain ⟨ι, _, m, p, hp, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist k 𝒢
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact p) inferInstance hp
    have := fun a ↦ finiteDimensional_H_twist (n := n) k (-(m a : ℤ)) q
    have : FiniteDimensional k
        ((∐ fun a ↦ ProjectiveSpace.twist n (Spec (.of k)) (-(m a : ℤ))).H q) :=
      Scheme.Modules.finiteDimensional_H_sigma k _ q
    have : FiniteDimensional k ((kernel p).H (q + 1)) := ih (kernel p) (q + 1) (by omega)
    have : FiniteDimensional k ((ShortComplex.kernelSequence p).X₂.H q) := ‹_›
    have : FiniteDimensional k ((ShortComplex.kernelSequence p).X₁.H (q + 1)) := ‹_›
    exact Scheme.Modules.finiteDimensional_H_of_shortExact k hS q

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {n : Type u} {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The cohomology of a coherent sheaf on a closed subscheme of `ℙᵈ_k` is finite-dimensional.**
For a closed immersion `i : X ⟶ ℙ(n; Spec k)` over `k` and a coherent `ℱ` on `X`, the coherent
`i_* ℱ` has the same cohomology as `ℱ`, `i` being affine
(`AlgebraicGeometry.Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`),
and this is `AlgebraicGeometry.ProjectiveSpace.finiteDimensional_H`. -/
theorem finiteDimensional_H_of_isClosedImmersion [Finite n] (i : X ⟶ ℙ(n; Spec (.of k)))
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i ℱ
  have := isFinitePresentation_pushforward_of_isClosedImmersion i ℱ
  have := ProjectiveSpace.finiteDimensional_H k ((pushforward i).obj ℱ) q
  obtain ⟨e⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k i q
  exact Module.Finite.equiv (R := k) (M := ((pushforward i).obj ℱ).H q)
    (e.app ⟨ℱ, inferInstance⟩).toLinearEquiv.symm

/-- The cohomology groups of every coherent sheaf on the `k`-scheme `X` are finite-dimensional.
This holds for closed subschemes of projective space
(`AlgebraicGeometry.Scheme.Modules.FiniteDimensionalH.of_isClosedImmersion`), in particular for a
`k`-scheme carrying an ample module (`AlgebraicGeometry.IsAmple.finiteDimensionalH`), and for every
proper `k`-scheme. -/
class FiniteDimensionalH (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] : Prop
    where
  finiteDimensional_H (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q)

/-- A closed subscheme of `ℙᵈ_k` has finite-dimensional coherent cohomology. -/
theorem FiniteDimensionalH.of_isClosedImmersion [Finite n] (i : X ⟶ ℙ(n; Spec (.of k)))
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] : FiniteDimensionalH k X :=
  ⟨fun ℱ _ _ q ↦ finiteDimensional_H_of_isClosedImmersion k i ℱ q⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- A `k`-scheme carrying a very ample module, that is, a closed subscheme of `ℙᵈ_k`, has
finite-dimensional coherent cohomology. -/
theorem IsVeryAmple.finiteDimensionalH {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (.of k))] {M : X.Modules} (h : IsVeryAmple (X ↘ Spec (.of k)) M) :
    Scheme.Modules.FiniteDimensionalH k X := by
  obtain ⟨n, i, _, _, hi, -⟩ := h
  have : i.IsOver (Spec (.of k)) := ⟨hi⟩
  exact .of_isClosedImmersion k i

/-- A `k`-scheme carrying an ample module, that is, a closed subscheme of `ℙᵈ_k`, has
finite-dimensional coherent cohomology. -/
theorem IsAmple.finiteDimensionalH {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (.of k))] {M : X.Modules} (h : IsAmple (X ↘ Spec (.of k)) M) :
    Scheme.Modules.FiniteDimensionalH k X :=
  h.2.choose_spec.2.finiteDimensionalH

end AlgebraicGeometry
