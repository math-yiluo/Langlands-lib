/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.RingTheory.Trace.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Riemann–Roch, Serre duality and the twist lemma for curves

Let `X` be a smooth proper curve over a field `k`. Its genus `g = dim_k H^1(X, 𝒪_X)` is
`AlgebraicGeometry.Scheme.arithmeticGenus`, and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an
invertible sheaf on it is `AlgebraicGeometry.Scheme.Modules.degree`. We state Riemann–Roch,
Serre duality with the canonical module `Ω¹_{X/k}`, and the two statements about line bundles on
the base change `X_K` of `X` along a field extension `K/k` that the Picard framework needs.

## Implementation notes

Riemann–Roch in the form `χ(𝒪_X) = 1 - g` needs `H⁰(X, 𝒪_X) = k`
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective`): `ℙ¹_ℂ` viewed as a curve over `ℝ` is
smooth and proper of genus `0`, but `χ(𝒪) = dim_ℝ ℂ = 2 ≠ 1 - 0`. Ampleness of line bundles of
positive degree needs it too: on `X = ℙ¹ ⊔ ℙ¹` the line bundle `𝒪(2) ⊔ 𝒪(-1)` has degree `1` but
is not ample. The statements about the degree of divisors and Serre duality do not need it.

The degree of a line bundle is *defined* cohomologically, as `deg ℒ = χ(ℒ) - χ(𝒪_X)`. Its
identification with the divisor degree is stated in three parts. An effective Cartier divisor
`D` is an invertible ideal sheaf `J = 𝒪_X(-D)`, its line bundle is `𝒪_X(D) = J.toModulesᵛ`, and
its degree is `dim_k Γ(D, 𝒪_D) = (J.subschemeι ≫ X ↘ Spec k).finrankΓ`. Then the χ-degree of
`𝒪_X(D)` is the degree of `D`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`), the χ-degree is
additive (`AlgebraicGeometry.Scheme.Modules.degree_tensorObj`), and every line bundle is
`𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` (`AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`).
Together they say that `deg ℒ = deg D₁ - deg D₂` is the divisor degree of `ℒ`, so that
`χ(ℒ) = deg D + 1 - g` is a genuine statement about divisors.

The blueprint states Riemann–Roch for *coherent* `ℱ`, with
`deg ℱ = length(torsion) + deg det(ℱ/torsion)`. The statements below assume `ℱ` finite
locally free, which is a genuine narrowing; it will have to be undone once coherence and the
torsion and determinant of a coherent sheaf exist.

The Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` is a `finsum`, so it is
junk unless the cohomology vanishes in large degrees. On a curve, quasi-coherent cohomology
vanishes in degrees `≥ 2` (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`, proved
through a finite morphism to `ℙ¹_k`), which is what makes the statements of this file about `χ`,
`deg` and the genus meaningful.

Ampleness is `AlgebraicGeometry.IsAmple` of
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, shared with the abelian-variety block.
The dual `ℱᵛ = Hom(ℱ, 𝒪_X)` of a sheaf of modules is the internal hom of
`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean`, and the tensor product is the monoidal
structure on `X.Modules` of `WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean`. The
canonical module is `Ω¹_{X/k} = AlgebraicGeometry.Scheme.Hom.relativeDifferentials` for curves
and `𝒪_X` in dimension `0`.

Serre duality is stated as the existence of a natural isomorphism between two functors on finite
locally free modules. The isomorphism is the one induced by the trace pairing
`H^q(ℱ) ⊗ H^p(ℱᵛ ⊗ ω_X) → H¹(ω_X) → k`, whose last map is the trace `t_X = ∑_x res_x`, the sum
over closed points of Tate's `k`-linear residues (Tate, *Residues of differentials on curves*).
At a point `x` with `κ(x)/k` separable, `res_x` is `Tr_{κ(x)/k}` of the classical residue.
This trace is `AlgebraicGeometry.Scheme.residueTrace`, and Serre duality for it is
`AlgebraicGeometry.Scheme.serreDuality_residueTrace`
(`WeilConjectures/AlgebraicGeometry/Curve/ResidueTrace.lean`).

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`,
  `AlgebraicGeometry.Scheme.Modules.degree_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`: the χ-degree is the
  divisor degree.
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos` and
  `AlgebraicGeometry.Scheme.isAmple_iff_degree_pos`: a line bundle is ample if and only if it
  has positive degree.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample line bundle is affine.
- `AlgebraicGeometry.Scheme.eulerChar_free_eq`, `AlgebraicGeometry.Scheme.eulerChar_unit_eq`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_add` and
  `AlgebraicGeometry.Scheme.finrankH_zero_eq`: Riemann–Roch for curves.
- `AlgebraicGeometry.Scheme.degree_relativeDifferentials`: `deg Ω¹_{X/k} = 2g - 2`.
- `AlgebraicGeometry.Scheme.serreDuality` and `AlgebraicGeometry.Scheme.serreDuality_zero`:
  Serre duality on curves and in dimension `0`.
- `AlgebraicGeometry.Scheme.finrankH_relativeDifferentials_zero_eq_arithmeticGenus` and
  `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`: `h⁰(Ω¹) = h¹(𝒪)`.
- `AlgebraicGeometry.Scheme.degree_eq_genus`: a line bundle with `h^0 = 1` and no higher
  cohomology has degree `g`.
- `AlgebraicGeometry.Scheme.exists_isInvertible_twist`: the twist lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

section Sections

/-- **A non-zero `H⁰` has a non-zero global section.** If `H⁰(X, ℳ) ≠ 0`, then there is a
non-zero morphism `s : 𝒪_X ⟶ ℳ`: `H⁰(X, ℳ) = Γ(X, ℳ)` and a global section `m` of `ℳ` is the
image of `1` under a unique `s : 𝒪_X ⟶ ℳ`. -/
theorem Modules.exists_ne_zero_of_nontrivial_H_zero {X : Scheme.{u}} (M : X.Modules)
    [Nontrivial (M.H 0)] : ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : M.H 0)
  let e := Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Limits.isTerminalTop (α := X.Opens))
  let m : Γ(M, ⊤) := e y
  have hm : m ≠ 0 := fun h ↦ hy (e.injective (h.trans e.map_zero.symm))
  let σ : M.sections := PresheafOfModules.sectionsMk
    (fun W ↦ M.val.map (homOfLE le_top : W.unop ⟶ ⊤).op m)
    (fun W _ f ↦ (ConcreteCategory.congr_hom (M.val.map_comp
        (homOfLE le_top : W.unop ⟶ ⊤).op f) _).symm)
  refine ⟨M.unitHomEquiv.symm σ, fun h ↦ hm ?_⟩
  have h1 := congrArg (fun s ↦ s.val (op ⊤)) (M.unitHomEquiv.apply_symm_apply σ)
  rw [h] at h1
  rw [SheafOfModules.unitHomEquiv_apply_coe] at h1
  have h2 : SheafOfModules.Hom.val (0 : 𝟙_ X.Modules ⟶ M) = 0 := rfl
  replace h1 : M.val.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op m = 0 := h1.symm
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from Subsingleton.elim _ _, op_id,
    M.val.map_id] at h1
  exact h1

/-- **A morphism `𝒪_X ⟶ N` which vanishes on `H⁰` is zero.** Under `H⁰(X, -) = Γ(X, -)` the
map `H⁰(σ)` sends `1` to the image of `1` under `σ`. -/
theorem Modules.eq_zero_of_forall_H_map_zero {X : Scheme.{u}} {N : X.Modules}
    (σ : 𝟙_ X.Modules ⟶ N) (h : ∀ z, H.map σ 0 z = 0) : σ = 0 := by
  refine eq_zero_of_app_top_one σ ?_
  have := Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map σ)
    ((Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj (𝟙_ X.Modules))
      isTerminalTop).symm (1 : Γ(X, ⊤)))
  rw [AddEquiv.apply_symm_apply] at this
  refine this.trans ?_
  erw [h]
  exact map_zero _

/-- **A rational point has degree one.** The closed subscheme of a `k`-rational point
`x : Spec k ⟶ X`, cut out by the ideal sheaf `ker x`, has `dim_k Γ(x, 𝒪) = 1`. -/
theorem Hom.finrankΓ_subschemeι_ker_fieldPoints {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : f.fieldPoints k) : (x.1.ker.subschemeι ≫ f).finrankΓ = 1 := by
  have hx : x.1 ≫ f = 𝟙 _ := by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [← Hom.finrankΓ_id (k := k)]
  refine Hom.finrankΓ_eq_of_iso _ _ (asIso x.1.toImage).symm (Iso.refl _) ?_
  rw [Iso.symm_hom, asIso_inv, Iso.refl_hom, Spec.map_id, Category.comp_id, Category.comp_id,
    IsIso.inv_eq_of_hom_inv_id]
  rw [← Category.assoc, Hom.toImage_imageι, hx]

/-- **Duals of invertible modules.** For an invertible `𝒪_X`-module `M`, the dual `Mᵛ` is
invertible, the evaluation `ev : M ⊗ Mᵛ ⟶ 𝒪_X`, `x ⊗ φ ↦ φ(x)`, is an isomorphism, and the
canonical biduality morphism `M ⟶ Mᵛᵛ` is an isomorphism.

(blueprint: `lem-pc-tensor-dual-invertible`) -/
theorem Modules.isInvertible_dual_and_isIso_dualEvaluation_and_isIso_bidual {X : Scheme.{u}}
    (M : X.Modules) [M.IsInvertible] :
    Mᵛ.IsInvertible ∧ IsIso (Modules.dualEvaluation M) ∧
      IsIso (SheafOfModules.bidual (R := X.sheaf) M) := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  exact ⟨inferInstance, inferInstance, SheafOfModules.isIso_bidual (R := X.sheaf) M⟩

end Sections


section FiniteScheme

variable {k : Type u} [Field k] {D : Scheme.{u}} [D.Over (Spec (.of k))]

/-- **`h⁰(D, 𝒪_D) = dim_k Γ(D, 𝒪_D)`**, using `H⁰(D, 𝒪_D) = Γ(D, 𝒪_D)`. -/
theorem Modules.finrankH_unit_zero_eq_finrankΓ :
    (𝟙_ D.Modules).finrankH k 0 = (D ↘ Spec (.of k)).finrankΓ := by
  let _ := (D ↘ Spec (.of k)).ΓAlgebra
  let e : (𝟙_ D.Modules).H 0 ≃ₗ[k] Γ(D, ⊤) :=
    { (H.zeroLinearEquiv (𝟙_ D.Modules)).toAddEquiv with
      map_smul' c x := (H.zeroLinearEquiv (𝟙_ D.Modules)).map_smul (globalSectionsRingHom k c) x }
  exact e.finrank_eq

/-- **Invertible modules on a finite `k`-scheme.** Let `D` be finite over a field `k` and `N` an
invertible `𝒪_D`-module. Then `h⁰(D, N) = dim_k Γ(D, 𝒪_D)`: the ring `Γ(D, 𝒪_D)` is artinian,
hence `D` is a finite discrete space (`AlgebraicGeometry.finite_and_discreteTopology_of_isFinite`).
Cohomology splits over its points
(`AlgebraicGeometry.Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint`), and on each of these
one-point schemes `N` is trivial
(`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit`). -/
theorem Modules.finrankH_zero_eq_finrankΓ_of_isFinite [IsFinite (D ↘ Spec (.of k))]
    (N : D.Modules) [N.IsInvertible] : N.finrankH k 0 = (D ↘ Spec (.of k)).finrankΓ := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_of_isFinite (D ↘ Spec (.of k))
  have : Fintype D := Fintype.ofFinite D
  -- `D` is the disjoint union of its finitely many points, on which `N` is trivial
  let U (p : D) : D.Opens := ⟨{p}, isOpen_discrete _⟩
  have hU : _root_.Pairwise (Function.onFun Disjoint U) := fun p q hpq ↦ by
    change Disjoint (U p) (U q)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_singleton.mpr hpq
  have hcover : ⨆ p, U p = ⊤ :=
    eq_top_iff.mpr fun p _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨p, rfl⟩
  rw [finrankH_eq_sum_of_pairwise_disjoint k U hU hcover N 0,
    ← finrankH_unit_zero_eq_finrankΓ, finrankH_eq_sum_of_pairwise_disjoint k U hU hcover _ 0]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  let : (U p).toScheme.Over (Spec (.of k)) := ⟨(U p).ι ≫ D ↘ Spec (.of k)⟩
  have : Subsingleton (U p) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (⟨p, rfl⟩ : U p) ((pullback (U p).ι).obj N)
  exact finrankH_congr k (e ≪≫ (pullbackObjUnitIso (U p).ι).symm) 0

end FiniteScheme

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

variable (k) in
include k in
/-- **Vanishing above the dimension of a curve.** On a smooth proper curve `X` over `k`,
`H^q(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and every `q ≥ 2`.

Choose a finite morphism `π : X ⟶ ℙ¹_k` (`exists_isFinite_flat_hom_projectiveLine`). As `π` is
affine, `H^q(X, ℱ) ≅ H^q(ℙ¹_k, π_* ℱ)` with `π_* ℱ` quasi-coherent
(`nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`), and the cohomology of a
quasi-coherent module on `ℙ¹_k`, which is computed by the Čech complex of the two standard affine
opens, vanishes in degrees `q ≥ 2` (`ProjectiveLine.subsingleton_H_of_two_le`). The blueprint
uses instead a cover of `X` by two affine opens.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Modules.subsingleton_H_of_two_le (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) := by
  obtain ⟨π, hπ, hfin, -, -, -⟩ := exists_isFinite_flat_hom_projectiveLine (k := k) (X := X)
  obtain ⟨e⟩ := Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k π q
  have := Modules.isQuasicoherent_pushforward_of_isAffineHom π ℱ
  have h := ProjectiveLine.subsingleton_H_of_two_le (k := k) ((Modules.pushforward π).obj ℱ) hq
  have h' : Subsingleton ((Modules.cohomologyFunctor k q).obj ((Modules.pushforward π).obj ℱ)) := h
  exact @Equiv.subsingleton _ _ (e.app ⟨ℱ, ‹_›⟩).toLinearEquiv.toEquiv h'

/-- **`χ = h⁰ - h¹` on a curve.** On a smooth proper curve `X` over `k`, the Euler
characteristic of every quasi-coherent `𝒪_X`-module `M` is `χ(M) = h⁰(M) - h¹(M)`, since
`H^q(X, M) = 0` for `q ≥ 2` (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`). -/
theorem Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    M.eulerChar k = M.finrankH k 0 - M.finrankH k 1 := by
  rw [Modules.eulerChar_eq_sum_range_of_subsingleton k M (D := 1) fun q hq ↦
    Modules.subsingleton_H_of_two_le k M hq]
  simp [Finset.sum_range_succ]
  ring

/-- For an ideal sheaf `J` and an invertible module `M`, the cokernel `M|_D` of
`J ⊗ M ⟶ 𝒪_X ⊗ M` is quasi-coherent. -/
lemma IdealSheafData.isQuasicoherent_cokernel_whiskerRight (J : X.IdealSheafData)
    (M : X.Modules) [M.IsInvertible] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (cokernel (J.toModulesι ▷ M)) := by
  have := Modules.isQuasicoherent_toModules J
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := Modules.isQuasicoherent_tensorObj J.toModules M
  have := Modules.isQuasicoherent_tensorObj (𝟙_ X.Modules) M
  exact Modules.isQuasicoherent_cokernel _

/-- **Effective divisors on curves are finite.** Let `D` be an effective Cartier divisor on a
smooth proper curve `X` over `k`, with invertible ideal sheaf `J`. Then `D` is finite over `k`:
it is proper over `k`, being closed in `X`, and quasi-finite, since a local equation of `D` is a
non-zerodivisor
(`IdealSheafData.IsInvertible.locallyQuasiFinite_subschemeι_comp_of_field`).

(blueprint: `def-pc-divisor-line-bundle`) -/
theorem IdealSheafData.IsInvertible.isFinite_subschemeι_comp {J : X.IdealSheafData}
    (hJ : J.IsInvertible) : IsFinite (J.subschemeι ≫ X ↘ Spec (.of k)) :=
  have := hJ.locallyQuasiFinite_subschemeι_comp_of_field (X ↘ Spec (.of k))
  IsFinite.of_isProper_of_locallyQuasiFinite _

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- **A line bundle restricted to an effective divisor, finiteness.** Let `D` be an effective
Cartier divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`,
and `M` an invertible `𝒪_X`-module. The cokernel `M|_D` of `J ⊗ M ⟶ 𝒪_X ⊗ M` has
finite-dimensional cohomology: it is the cohomology of the invertible module `ι^* M` on the
proper `k`-scheme `D`. -/
theorem IdealSheafData.IsInvertible.finiteDimensional_H_cokernel_whiskerRight
    {J : X.IdealSheafData} (_hJ : J.IsInvertible) (M : X.Modules) [M.IsInvertible] (q : ℕ) :
    FiniteDimensional k ((cokernel (J.toModulesι ▷ M)).H q) := by
  let : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : IsProper (J.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (J.subschemeι ≫ X ↘ Spec (.of k)))
  obtain ⟨e⟩ := J.nonempty_H_cokernel_whiskerRight_linearEquiv k M q
  exact e.symm.finiteDimensional

variable (k) in
include k in
/-- **A line bundle restricted to an effective divisor, vanishing of `H¹`.** Let `D` be an
effective Cartier divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf
`J = 𝒪_X(-D)`, and `M` an invertible `𝒪_X`-module. The cokernel `M|_D` of `J ⊗ M ⟶ 𝒪_X ⊗ M` has
`H¹(X, M|_D) = 0`: its cohomology is that of `ι^* M` on the finite, hence affine, `k`-scheme `D`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_subschemeι_comp`). -/
theorem IdealSheafData.IsInvertible.subsingleton_H_one_cokernel_whiskerRight
    {J : X.IdealSheafData} (hJ : J.IsInvertible) (M : X.Modules) [M.IsInvertible] :
    Subsingleton ((cokernel (J.toModulesι ▷ M)).H 1) := by
  have := hJ.isFinite_subschemeι_comp (k := k)
  have : IsAffine J.subscheme := isAffine_of_isAffineHom (J.subschemeι ≫ X ↘ Spec (.of k))
  have := Modules.subsingleton_H_succ_of_isAffine ((Modules.pullback J.subschemeι).obj M) 0
  obtain ⟨e⟩ := J.nonempty_H_cokernel_whiskerRight_linearEquiv k M 1
  exact e.toEquiv.subsingleton

/-- **A line bundle restricted to an effective divisor, Euler characteristic.** Let `D` be an
effective Cartier divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf
`J = 𝒪_X(-D)`, and `M` an invertible `𝒪_X`-module. The cokernel `M|_D` of `J ⊗ M ⟶ 𝒪_X ⊗ M` has
`χ(M|_D) = deg D = dim_k Γ(D, 𝒪_D)`.

Its cohomology is that of `ι^* M` on the finite `k`-scheme `D`, which vanishes in positive
degrees, and `h⁰(D, ι^* M) = dim_k Γ(D, 𝒪_D)`
(`AlgebraicGeometry.Scheme.Modules.finrankH_zero_eq_finrankΓ_of_isFinite`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`, part (2)) -/
theorem IdealSheafData.IsInvertible.eulerChar_cokernel_whiskerRight {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (M : X.Modules) [M.IsInvertible] :
    (cokernel (J.toModulesι ▷ M)).eulerChar k = (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
  let : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : IsFinite (J.subscheme ↘ Spec (.of k)) := hJ.isFinite_subschemeι_comp (k := k)
  have := hJ.subsingleton_H_one_cokernel_whiskerRight k M
  obtain ⟨e⟩ := J.nonempty_H_cokernel_whiskerRight_linearEquiv k M 0
  have h₀ : Modules.finrankH k (cokernel (J.toModulesι ▷ M)) 0 =
      (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
    rw [Modules.finrankH, e.finrank_eq]
    exact Modules.finrankH_zero_eq_finrankΓ_of_isFinite _
  have h₁ : Modules.finrankH k (cokernel (J.toModulesι ▷ M)) 1 = 0 :=
    Module.finrank_zero_of_subsingleton
  have := J.isQuasicoherent_cokernel_whiskerRight M
  rw [Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, h₀, h₁]
  simp

/-- **The degree of a line bundle twisted by an effective divisor.** Let `D` be an effective
Cartier divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`,
and `ℒ` an invertible `𝒪_X`-module. Then `χ(ℒ ⊗ 𝒪_X(D)) = χ(ℒ) + deg D`, where
`deg D = dim_k Γ(D, 𝒪_D)`.

Write `M = ℒ ⊗ 𝒪_X(D)`. Tensoring `0 → J → 𝒪_X → 𝒪_D → 0` with `M` gives the short exact
sequence `0 → J ⊗ M → M → M|_D → 0`, where `J ⊗ M ≅ ℒ` since `J ⊗ 𝒪_X(D) ≅ 𝒪_X`. The Euler
characteristic is additive in short exact sequences
(`AlgebraicGeometry.Scheme.Modules.eulerChar_eq_add_of_shortExact`), and `χ(M|_D) = deg D`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_cokernel_whiskerRight`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`, part (2)) -/
theorem IdealSheafData.IsInvertible.eulerChar_tensorObj_dual_toModules {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (ℒ : X.Modules) [ℒ.IsInvertible] :
    (ℒ ⊗ J.toModulesᵛ).eulerChar k =
      ℒ.eulerChar k + (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
  have := hJ.isInvertible_toModules
  have := hJ.isInvertible_dual_toModules
  let M := ℒ ⊗ J.toModulesᵛ
  let S := ShortComplex.mk (J.toModulesι ▷ M) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have e₂ : S.X₂ ≅ M := λ_ M
  have : S.X₂.IsInvertible := Modules.IsInvertible.of_iso e₂.symm
  have := hJ.finiteDimensional_H_cokernel_whiskerRight (k := k) M
  have := J.isQuasicoherent_cokernel_whiskerRight M
  have := Modules.isQuasicoherent_toModules J
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁ :=
    Modules.isQuasicoherent_tensorObj J.toModules M
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₂ :=
    Modules.IsInvertible.isQuasicoherent _
  have h := Modules.eulerChar_eq_add_of_shortExact k hS 1
    (fun q hq ↦ Modules.subsingleton_H_of_two_le k _ (by omega))
    (fun q hq ↦ Modules.subsingleton_H_of_two_le k _ (by omega))
    (fun q hq ↦ Modules.subsingleton_H_of_two_le k _ (by omega))
  obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit J.toModules
  have e₁ : S.X₁ ≅ ℒ := (α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso ℒ d ≪≫ ρ_ ℒ
  rw [Modules.eulerChar_congr k e₁, Modules.eulerChar_congr k e₂,
    hJ.eulerChar_cokernel_whiskerRight] at h
  exact h

/-- **Riemann–Roch for curves, divisor degree.** Let `D` be an effective Cartier divisor on a
smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`. Then the χ-degree
`χ(𝒪_X(D)) - χ(𝒪_X)` of its line bundle `𝒪_X(D) = J.toModulesᵛ` is the degree
`dim_k Γ(D, 𝒪_D) = ∑_x n_x [κ(x) : k]` of `D`. With
`AlgebraicGeometry.Scheme.eulerChar_unit_eq` this is `χ(𝒪_X(D)) = deg D + 1 - g`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem IdealSheafData.IsInvertible.degree_dual_toModules {J : X.IdealSheafData}
    (hJ : J.IsInvertible) :
    J.toModulesᵛ.degree k = (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
  have h := hJ.eulerChar_tensorObj_dual_toModules (k := k) (𝟙_ X.Modules)
  rw [Modules.eulerChar_congr k (λ_ _)] at h
  have hu : Modules.eulerChar k (𝟙_ X.Modules) =
      Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) := rfl
  rw [Modules.degree, h, hu, add_sub_cancel_left]

/-- **The line bundle of a rational point has degree one.** Let `D` be an effective Cartier
divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`, which is
a `k`-rational point: `Γ(D, 𝒪_D) = k` is one-dimensional. Then the χ-degree of `𝒪_X(D)` of
blueprint `def-pc-degree-line-bundle` is `1`, the degree of the divisor `[P]` of
`corollary-degree-jacobian--1`. For an arbitrary effective `D` the agreement of the two degrees is
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem IdealSheafData.IsInvertible.degree_dual_toModules_eq_one {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (h : (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ = 1) :
    J.toModulesᵛ.degree k = 1 := by
  rw [hJ.degree_dual_toModules, h, Nat.cast_one]

include k in
/-- **The degree of a multiple of a divisor.** For an effective Cartier divisor `D` on a smooth
proper curve, `deg (n D) = n deg D`, by additivity of the degree of divisors
(`AlgebraicGeometry.Scheme.IdealSheafData.finrankΓ_subschemeι_mul_comp`). -/
theorem IdealSheafData.IsInvertible.finrankΓ_subschemeι_pow_comp {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (n : ℕ) :
    ((J ^ n).subschemeι ≫ X ↘ Spec (.of k)).finrankΓ =
      n * (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
  induction n with
  | zero =>
    rw [zero_mul, pow_zero, IdealSheafData.one_eq_top]
    let := ((⊤ : X.IdealSheafData).subschemeι ≫ X ↘ Spec (.of k)).ΓAlgebra
    exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
    have := hJ.isFinite_subschemeι_comp (k := k)
    have := (hJ.pow n).isFinite_subschemeι_comp (k := k)
    have : IsFinite ((J ^ n * J).subschemeι ≫ X ↘ Spec (.of k)) :=
      ((hJ.pow n).mul hJ).isFinite_subschemeι_comp
    rw [pow_succ, IdealSheafData.finrankΓ_subschemeι_mul_comp _ (hJ.pow n) hJ, ih, Nat.succ_mul]

/-- **Twisting by a large multiple of a divisor produces sections.** Let `D` be a non-empty
effective Cartier divisor on a smooth proper curve, with invertible ideal sheaf `J = 𝒪_X(-D)`,
and `ℒ` an invertible sheaf. Then `H⁰(X, ℒ ⊗ 𝒪_X(n D)) ≠ 0` for all `n ≫ 0`: by
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_tensorObj_dual_toModules`,
`h⁰ ≥ χ(ℒ ⊗ 𝒪_X(n D)) = χ(ℒ) + deg (n D) ≥ χ(ℒ) + n`. -/
theorem Modules.exists_finrankH_zero_pos_tensorObj_dual_pow (ℒ : X.Modules) [ℒ.IsInvertible]
    {J : X.IdealSheafData} (hJ : J.IsInvertible) (hne : (J.support : Set X).Nonempty) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 0 < (ℒ ⊗ (J ^ n).toModulesᵛ).finrankH k 0 := by
  have : Nonempty J.subscheme := by
    obtain ⟨x, hx⟩ := hne
    rw [← IdealSheafData.range_subschemeι] at hx
    obtain ⟨y, -⟩ := hx
    exact ⟨y⟩
  have := hJ.isFinite_subschemeι_comp (k := k)
  have hd := Hom.finrankΓ_pos_of_isFinite (J.subschemeι ≫ X ↘ Spec (.of k))
  refine ⟨(1 - ℒ.eulerChar k).toNat, fun n hn ↦ ?_⟩
  have h₁ := (hJ.pow n).eulerChar_tensorObj_dual_toModules (k := k) ℒ
  have := (hJ.pow n).isInvertible_dual_toModules
  have := Modules.IsInvertible.isQuasicoherent (ℒ ⊗ (J ^ n).toModulesᵛ)
  have h₂ := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k)
    (ℒ ⊗ (J ^ n).toModulesᵛ)
  have h₃ := (hJ.finrankΓ_subschemeι_pow_comp (k := k) n).ge.trans'
    (Nat.le_mul_of_pos_right n hd)
  have h₄ := Int.self_le_toNat (1 - ℒ.eulerChar k)
  omega

include k in
attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Every line bundle has a section with divisorial zeros after a twist.** For every invertible
sheaf `ℒ` on a smooth proper curve there is an effective Cartier divisor `D₂`, with invertible
ideal sheaf `J₂ = 𝒪_X(-D₂)`, and a global section `s` of `ℒ ⊗ 𝒪_X(D₂)` whose zero scheme is an
effective Cartier divisor, i.e. `s` does not vanish identically on any connected component.

Choose a closed point `x i` on each of the finitely many connected components `V i` of `X`, and
let `D = ∑ᵢ x i`, an effective Cartier divisor meeting every component. Each `V i` is a smooth
proper curve, so `ℒ ⊗ 𝒪_X(n D)` has a non-zero section on `V i` for `n ≫ 0`
(`AlgebraicGeometry.Scheme.Modules.exists_finrankH_zero_pos_tensorObj_dual_pow`). These glue to
a global section `s`, since `X` is the disjoint union of the `V i`. Its zero scheme is locally
principal, and non-zero on each `V i`, which is integral; hence it is invertible
(`AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal.isInvertible`).

(blueprint: part of the proof of `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Modules.exists_isInvertible_zeroLocus_tensorObj_dual (ℒ : X.Modules) [ℒ.IsInvertible] :
    ∃ J₂ : X.IdealSheafData, J₂.IsInvertible ∧
      ∃ s : 𝟙_ X.Modules ⟶ ℒ ⊗ J₂.toModulesᵛ, (Modules.Hom.zeroLocus s).IsInvertible := by
  classical
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  -- the finitely many connected components `V i` of `X`, open and closed
  let m := Nat.card (ConnectedComponents X)
  have : Finite (ConnectedComponents X) := inferInstance
  let e : ConnectedComponents X ≃ Fin m := Finite.equivFin _
  let V (i : Fin m) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {e.symm i}, (isOpen_discrete {e.symm i}).preimage
      ConnectedComponents.continuous_coe⟩
  have hV : _root_.Pairwise (Function.onFun Disjoint V) := fun i j hij ↦
    TopologicalSpace.Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr
      (e.symm.injective.ne hij)).preimage ConnectedComponents.mk)
  have hcover : ⨆ i, V i = ⊤ := eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨e (ConnectedComponents.mk x), by simp [V]⟩
  have hclosed (i : Fin m) : IsClosed (V i : Set X) :=
    (isClosed_discrete {e.symm i}).preimage ConnectedComponents.continuous_coe
  have hne (i : Fin m) : (V i : Set X).Nonempty := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm i)
    exact ⟨x, hx⟩
  have hconn (i : Fin m) : ConnectedSpace (V i) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm i)
    have : (V i : Set X) = connectedComponent x := by
      change ConnectedComponents.mk ⁻¹' {e.symm i} = _
      rw [← hx]
      exact connectedComponents_preimage_singleton
    exact isConnected_iff_connectedSpace.mp (this ▸ isConnected_connectedComponent)
  -- each `V i` is a smooth proper curve
  let (i : Fin m) : (V i).toScheme.Over (Spec (.of k)) := ⟨(V i).ι ≫ X ↘ Spec (.of k)⟩
  have (i : Fin m) : IsClosedImmersion (V i).ι := .of_isPreimmersion _ (by simpa using hclosed i)
  have (i : Fin m) : SmoothOfRelativeDimension 1 ((V i).toScheme ↘ Spec (.of k)) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) (V i).ι (X ↘ Spec (.of k))
    rwa [zero_add] at this
  have (i : Fin m) : IsProper ((V i).toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper ((V i).ι ≫ X ↘ Spec (.of k)))
  -- a closed point `x i` on each component, and the divisor `D = ∑ x i`
  have : CompactSpace X := inferInstance
  choose x hxV hxcl using fun i ↦ (hclosed i).exists_closed_singleton (hne i)
  let J : X.IdealSheafData := ∏ i, IdealSheafData.vanishingIdeal ⟨{x i}, hxcl i⟩
  have hJ : J.IsInvertible := Finset.prod_induction _
    (fun I : X.IdealSheafData ↦ I.IsInvertible)
    (fun _ _ ha hb ↦ ha.mul hb) IdealSheafData.isInvertible_top fun i _ ↦
      isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one (X ↘ Spec (.of k)) (hxcl i)
  have hJx (i : Fin m) : x i ∈ J.support := by
    have hle : J ≤ IdealSheafData.vanishingIdeal ⟨{x i}, hxcl i⟩ := by
      change ∏ j, _ ≤ _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      exact mul_le_of_le_one_right bot_le le_top
    exact IdealSheafData.le_support_iff_le_vanishingIdeal.mpr hle rfl
  -- on each component, twisting by `n D` for `n ≫ 0` produces non-zero sections
  have hI (i : Fin m) : (J.comap (V i).ι).IsInvertible := hJ.comap_of_isOpenImmersion _
  have hIne (i : Fin m) : ((J.comap (V i).ι).support : Set (V i)).Nonempty :=
    ⟨⟨x i, hxV i⟩, by rw [IdealSheafData.coe_support_comap]; exact hJx i⟩
  choose n₀ hn₀ using fun i ↦ exists_finrankH_zero_pos_tensorObj_dual_pow (k := k)
    ((pullback (V i).ι).obj ℒ) (hI i) (hIne i)
  let n := Finset.univ.sup n₀
  have := (hJ.pow n).isInvertible_dual_toModules
  let M := ℒ ⊗ (J ^ n).toModulesᵛ
  let N (i : Fin m) : X.Modules := (pushforward (V i).ι).obj ((restrictFunctor (V i).ι).obj M)
  have hpos (i : Fin m) : 0 < (N i).finrankH k 0 := by
    have h := hn₀ i n (Finset.le_sup (Finset.mem_univ i))
    rw [← IdealSheafData.comap_pow] at h
    obtain ⟨e₁⟩ := nonempty_pullback_tensorObj_iso (V i).ι ℒ (J ^ n).toModulesᵛ
    obtain ⟨e₂⟩ := (hJ.pow n).nonempty_pullback_dual_toModules_iso (V i).ι
      ((hJ.pow n).comap_of_isOpenImmersion _)
    rw [finrankH_pushforward_ι (V i) (hclosed i) k,
      finrankH_congr k ((restrictFunctorIsoPullback (V i).ι).app M ≪≫ e₁ ≪≫
        whiskerLeftIso _ e₂)]
    exact h
  have hτ (i : Fin m) : ∃ τ : 𝟙_ X.Modules ⟶ N i, τ ≠ 0 := by
    have : Nontrivial ((N i).H 0) := Module.nontrivial_of_finrank_pos (R := k) (hpos i)
    exact exists_ne_zero_of_nontrivial_H_zero _
  choose τ hτ using hτ
  -- glue them to a global section `s`, using `M ≅ ⨁ᵢ (V i).ι_* (M|_{V i})`
  let φ : M ⟶ ⨁ N := biproduct.lift fun i ↦ (restrictAdjunction (V i).ι).unit.app M
  have : IsIso φ := isIso_biproduct_lift_restrictAdjunction_unit V hV hcover M
  let s : 𝟙_ X.Modules ⟶ M := biproduct.lift τ ≫ inv φ
  have hs (i : Fin m) : s ≫ (restrictAdjunction (V i).ι).unit.app M = τ i := by
    have h : s ≫ φ = biproduct.lift τ := by simp [s]
    simpa [φ] using congrArg (· ≫ biproduct.π N i) h
  refine ⟨J ^ n, hJ.pow n, s, ?_⟩
  -- the zero scheme of `s` is invertible on each (integral) component
  refine IdealSheafData.IsInvertible.of_iSup_opensRange_eq_top (fun i ↦ (V i).ι)
    (by simpa using hcover) fun i ↦ ?_
  have : Smooth ((V i).toScheme ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular (V i) := IsRegular.of_smooth ((V i).toScheme ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian ((V i).toScheme ↘ Spec (.of k))
  have : IsIntegral (V i) := IsRegular.isIntegral _
  have := IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have := IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback (V i).ι).obj (𝟙_ X.Modules)) :=
    IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback (V i).ι).obj M) :=
    IsInvertible.sheafOfModules_isInvertible _
  rw [Hom.comap_zeroLocus]
  refine (Hom.isLocallyPrincipal_zeroLocus _).isInvertible fun h ↦ hτ i ?_
  rw [Hom.zeroLocus_eq_bot_iff] at h
  have h' : (restrictFunctor (V i).ι).map s = 0 := by
    have := (restrictFunctorIsoPullback (V i).ι).hom.naturality s
    rw [h, comp_zero] at this
    exact (cancel_mono _).mp (this.trans zero_comp.symm)
  have := (restrictAdjunction (V i).ι).unit.naturality s
  simp only [Functor.id_map, Functor.comp_map, h', Functor.map_zero, comp_zero] at this
  rw [← hs i, this]


include k in
/-- **Every line bundle comes from a divisor.** Every invertible sheaf `ℒ` on a smooth proper
curve is `𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` for effective Cartier divisors `D₁` and `D₂`, given by
invertible ideal sheaves `J₁ = 𝒪_X(-D₁)` and `J₂ = 𝒪_X(-D₂)`: `ℒ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`.

Twisting by a suitable `D₂`, the invertible sheaf `ℒ ⊗ 𝒪_X(D₂)` has a global section `s` whose
zero scheme `D₁` is an effective Cartier divisor
(`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_zeroLocus_tensorObj_dual`), and then
`ℒ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`
(`AlgebraicGeometry.Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj`).

With `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules` and
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` this gives `deg ℒ = deg D₁ - deg D₂`: the
χ-degree of every line bundle is its divisor degree.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Modules.exists_tensorObj_dual_toModules_iso (ℒ : X.Modules) [ℒ.IsInvertible] :
    ∃ J₁ J₂ : X.IdealSheafData, J₁.IsInvertible ∧ J₂.IsInvertible ∧
      Nonempty (ℒ ⊗ₘ J₂.toModulesᵛ ≅ J₁.toModulesᵛ) := by
  obtain ⟨J₂, h₂, s, hs⟩ := Modules.exists_isInvertible_zeroLocus_tensorObj_dual (k := k) ℒ
  have := h₂.isInvertible_dual_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible (ℒ ⊗ J₂.toModulesᵛ)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj s hs
  exact ⟨_, J₂, hs, h₂, ⟨e ≪≫ ρ_ _⟩⟩

/-- **The degree is additive.** `deg (ℒ ⊗ ℳ) = deg ℒ + deg ℳ` for invertible sheaves on a smooth
proper curve.

Write `ℳ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`
(`AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`); twisting by the
effective divisors `D₁` and `D₂`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_tensorObj_dual_toModules`)
adds their degrees to `χ`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem Modules.degree_tensorObj (ℒ ℳ : X.Modules) [ℒ.IsInvertible] [ℳ.IsInvertible] :
    (ℒ ⊗ₘ ℳ).degree k = ℒ.degree k + ℳ.degree k := by
  obtain ⟨J₁, J₂, h₁, h₂, ⟨e⟩⟩ := Modules.exists_tensorObj_dual_toModules_iso (k := k) ℳ
  have := h₁.isInvertible_dual_toModules
  have := h₂.isInvertible_dual_toModules
  have a := h₂.eulerChar_tensorObj_dual_toModules (k := k) (ℒ ⊗ ℳ)
  have b := h₁.eulerChar_tensorObj_dual_toModules (k := k) ℒ
  have c := h₂.eulerChar_tensorObj_dual_toModules (k := k) ℳ
  have d := h₁.degree_dual_toModules (k := k)
  rw [Modules.eulerChar_congr k (α_ _ _ _ ≪≫ whiskerLeftIso ℒ e)] at a
  rw [Modules.eulerChar_congr k e] at c
  simp only [Modules.degree] at d ⊢
  linarith

/-- The degree of the dual: `deg ℒᵛ = -deg ℒ`, since `ℒ ⊗ ℒᵛ ≅ 𝒪_X`. -/
theorem Modules.degree_dual (ℒ : X.Modules) [ℒ.IsInvertible] : ℒᵛ.degree k = -ℒ.degree k := by
  obtain ⟨e⟩ := Modules.nonempty_tensorObj_dual_iso_unit ℒ
  have h := Modules.degree_tensorObj (k := k) ℒ ℒᵛ
  rw [Modules.degree_congr k e] at h
  have hu : Modules.degree k (𝟙_ X.Modules) = 0 := Modules.degree_unit (X := X) k
  linarith

/-- The degree of a tensor power: `deg ℒ^{⊗ n} = n deg ℒ`. -/
theorem Modules.degree_tensorPow (ℒ : X.Modules) [ℒ.IsInvertible] (n : ℕ) :
    (ℒ.tensorPow n).degree k = n * ℒ.degree k := by
  induction n with
  | zero => exact (Modules.degree_unit (X := X) k).trans (by simp)
  | succ n ih =>
    rw [Modules.tensorPow_succ, Modules.degree_tensorObj, ih]
    push_cast
    ring

omit [IsProper (X ↘ Spec (.of k))] in
/-- **Rational points are Cartier divisors on smooth curves.** The ideal sheaf `ker x` of a
`k`-rational point `x : Spec k ⟶ X` of a smooth curve `X` over `k` is invertible: the local ring
`𝒪_{X,x}` is regular of dimension one, hence a discrete valuation ring, and its maximal ideal,
the stalk of `ker x`, is generated by a uniformizer.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Hom.isInvertible_ker_fieldPoints (x : (X ↘ Spec (.of k)).fieldPoints k) :
    x.1.ker.IsInvertible :=
  Hom.isInvertible_ker_of_smoothOfRelativeDimension_one (X ↘ Spec (.of k)) x.1 (by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])

/-- **The ideal sheaf of a rational point has degree `-1`.** For a `k`-rational point `x` of a
smooth proper curve, `𝒪_X(-x) = ker x` has degree `-1`: its dual `𝒪_X(x)` has degree
`dim_k Γ(x, 𝒪_x) = 1`, and `𝒪_X(-x) ⊗ 𝒪_X(x) ≅ 𝒪_X`. -/
theorem degree_toModules_ker_fieldPoints (x : (X ↘ Spec (.of k)).fieldPoints k) :
    x.1.ker.toModules.degree k = -1 := by
  have hJ := Hom.isInvertible_ker_fieldPoints x
  have := hJ.isInvertible_toModules
  have := hJ.isInvertible_dual_toModules
  obtain ⟨e⟩ := Modules.nonempty_tensorObj_dual_iso_unit x.1.ker.toModules
  have h := Modules.degree_tensorObj (k := k) x.1.ker.toModules x.1.ker.toModulesᵛ
  rw [Modules.degree_congr k e, hJ.degree_dual_toModules_eq_one
    ((X ↘ Spec (.of k)).finrankΓ_subschemeι_ker_fieldPoints x)] at h
  have h0 : Modules.degree k (𝟙_ X.Modules) = 0 := Modules.degree_unit k
  omega

end Curve

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GlobalSectionsBijective k X]

/-- **Riemann–Roch for curves, structure sheaf.** `χ(𝒪_X) = 1 - g` on a smooth proper curve `X`
over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`: `χ(𝒪_X) = h⁰(𝒪_X) - h¹(𝒪_X)` with
`h⁰(𝒪_X) = 1`.

Without the hypothesis `H⁰(X, 𝒪_X) = k` the statement fails, as for `ℙ¹_ℂ` over `ℝ`, where
`χ(𝒪) = 2`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem eulerChar_unit_eq :
    Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) =
      1 - (arithmeticGenus k X : ℤ) := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  refine (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one
    (SheafOfModules.unit X.ringCatSheaf)).trans ?_
  rw [Modules.finrankH_unit_zero]
  rfl

/-- **Riemann–Roch for curves, free case.** The Euler characteristic of the free sheaf of rank
`r` on a smooth proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, is
`χ(𝒪_X^{⊕ r}) = r (1 - g)`: cohomology commutes with finite direct sums
(`AlgebraicGeometry.Scheme.Modules.finrankH_of_isBilimit`).

Together with `AlgebraicGeometry.Scheme.Modules.degree`, which measures the degree of a
rank-`r` sheaf against `𝒪_X^{⊕ r}`, this is the content of the Riemann–Roch identity
`χ(ℱ) = deg ℱ + r (1 - g)`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem eulerChar_free_eq (r : ℕ) :
    Modules.eulerChar (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) =
      r * (1 - (arithmeticGenus k X : ℤ)) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_free (R := X.ringCatSheaf) (ULift.{u} (Fin r))
  have hb := biconeIsBilimitOfColimitCoconeOfIsColimit
    (colimit.isColimit (Discrete.functor fun _ : ULift.{u} (Fin r) ↦ O))
  have (q : ℕ) : FiniteDimensional k (O.H q) :=
    Modules.finiteDimensional_H (M := 𝟙_ X.Modules) k q
  have h (q : ℕ) : Modules.finrankH (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) q =
      r * O.finrankH k q :=
    (Modules.finrankH_of_isBilimit k hb q).trans (by simp)
  refine (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one _).trans ?_
  have hO := (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k) O).symm.trans
    (eulerChar_unit_eq (k := k))
  simp only [h, Nat.cast_mul, ← hO]
  ring

/-- **Riemann–Roch for line bundles.** `χ(ℒ) = deg ℒ + 1 - g` for every invertible `ℒ` on a
smooth proper curve with `H⁰(X, 𝒪_X) = k`, of genus `g`, where by
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` and
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules` the degree is the
divisor degree.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`, part (1)) -/
theorem Modules.eulerChar_eq_degree_add (ℒ : X.Modules) :
    ℒ.eulerChar k = ℒ.degree k + 1 - arithmeticGenus k X := by
  rw [Modules.degree, eulerChar_unit_eq]
  ring

end RiemannRoch

section Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Serre duality for curves.** Let `X` be a smooth proper curve over `k` with canonical module
`ω_X = Ω¹_{X/k}`, and let `p + q = 1`. Then `ℱ ↦ H^q(X, ℱ)^∨` and `ℱ ↦ H^p(X, ℱᵛ ⊗ Ω¹_{X/k})`
are naturally isomorphic as contravariant functors on finite locally free `ℱ`. That is, there are
`k`-linear isomorphisms `e ℱ : H^q(X, ℱ)^∨ ≅ H^p(X, ℱᵛ ⊗ Ω¹_{X/k})` such that for every
morphism `φ : ℱ ⟶ 𝒢` of finite locally free modules the square
```
  H^q(𝒢)^∨ ───── e 𝒢 ─────▶ H^p(𝒢ᵛ ⊗ Ω¹)
     │                           │
 H^q(φ)^∨                   H^p(φᵛ ▷ Ω¹)
     ▼                           ▼
  H^q(ℱ)^∨ ───── e ℱ ─────▶ H^p(ℱᵛ ⊗ Ω¹)
```
commutes. No hypothesis `H⁰(X, 𝒪_X) = k` is needed.

The case `q = 1` is `AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso`, obtained from a finite flat
morphism `X ⟶ ℙ¹_k` and duality on `ℙ¹_k`; the case `q = 0` is
`AlgebraicGeometry.Scheme.nonempty_dual_H_zero_iso`, deduced from it by biduality.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem serreDuality [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (p q : ℕ) (hpq : p + q = 1) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k q).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k p) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0 := by omega
  · exact nonempty_dual_H_one_iso
  · exact nonempty_dual_H_zero_iso

/-- **Trace duality on a finite étale scheme over `k`.** Let `X` be affine with `Γ(X, ⊤)` étale
over `k`, and let `ℱ` be quasi-coherent. Then `x ↦ (m ↦ Tr(x(m)))`, pairing a global section `x`
of `ℱᵛ` (a morphism `ℱ ⟶ 𝒪_X`) with a global section `m` of `ℱ` and taking the trace of
`Γ(X, ⊤)` over `k`, is a `k`-linear isomorphism `H⁰(X, ℱᵛ) ≃ H⁰(X, ℱ)^∨`. -/
theorem exists_linearEquiv_dual_H_zero_of_etale [IsAffine X]
    (hX : (globalSectionsRingHom k (X := X)).Etale) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    ∃ e : (ℱᵛ).H 0 ≃ₗ[k] Module.Dual k (ℱ.H 0), ∀ x m, e x m =
      Algebra.trace k Γ(X, ⊤) ((Modules.homObjHZeroAddEquiv ℱ (SheafOfModules.unit _) x).app ⊤
        (Modules.H.zeroLinearEquiv ℱ m)) := by
  let := (globalSectionsRingHom k (X := X)).toAlgebra
  have : Algebra.Etale k Γ(X, ⊤) := hX
  set Φ := Modules.homObjHZeroAddEquiv ℱ (SheafOfModules.unit X.ringCatSheaf)
  set z := Modules.H.zeroLinearEquiv ℱ
  -- `Γ(ℱ, ⊤)` as a `k`-module, by restricting scalars along `k → Γ(X, ⊤)`
  let : Module k Γ(ℱ, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
  have : IsScalarTower k Γ(X, ⊤) Γ(ℱ, ⊤) := ⟨fun c a m ↦ by
    change (c • a) • m = algebraMap k Γ(X, ⊤) c • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let D := Algebra.Etale.linearMapEquivDual k Γ(X, ⊤) Γ(ℱ, ⊤)
  -- the `Γ(X, ⊤)`-linear map on global sections of a morphism `ℱ ⟶ 𝒪_X`
  let appₗ (φ : ℱ ⟶ SheafOfModules.unit X.ringCatSheaf) : Γ(ℱ, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    { toFun := φ.app ⊤
      map_add' := map_add _
      map_smul' a m := Modules.Hom.app_smul φ a m }
  have hz (c : k) (m : ℱ.H 0) : z (c • m) = c • z m := by
    rw [Modules.smul_H_eq_globalSectionsRingHom_smul, LinearEquiv.map_smul]
    rfl
  let L : (ℱᵛ).H 0 →ₗ[k] Module.Dual k (ℱ.H 0) :=
    { toFun x :=
        { toFun m := Algebra.trace k Γ(X, ⊤) ((Φ x).app ⊤ (z m))
          map_add' m m' := by simp only [map_add]
          map_smul' c m := by
            change Algebra.trace k Γ(X, ⊤) (appₗ (Φ x) (z (c • m))) = c * _
            rw [hz, LinearMap.map_smul_of_tower, map_smul, smul_eq_mul]
            rfl }
      map_add' x y := by
        ext m
        simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [show ((Φ x + Φ y).app ⊤) (z m) = (Φ x).app ⊤ (z m) + (Φ y).app ⊤ (z m) from rfl,
          map_add]
      map_smul' c x := by
        ext m
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          smul_eq_mul]
        rw [Modules.smul_H_eq_globalSectionsRingHom_smul, Modules.homObjHZeroAddEquiv_smul]
        change Algebra.trace k Γ(X, ⊤) ((Modules.smulHom _ _).app ⊤ ((Φ x).app ⊤ (z m))) = _
        rw [Modules.smulHom_app_top_apply, smul_eq_mul]
        change Algebra.trace k Γ(X, ⊤) (algebraMap k Γ(X, ⊤) c * _) = _
        rw [← Algebra.smul_def, map_smul, smul_eq_mul] }
  refine ⟨LinearEquiv.ofBijective L ⟨fun x y h ↦ ?_, fun l ↦ ?_⟩, fun x m ↦ rfl⟩
  · have h0 (m : ℱ.H 0) : Algebra.trace k Γ(X, ⊤) ((Φ (x - y)).app ⊤ (z m)) = 0 := by
      have := congr($h m)
      rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub] at this
      exact this
    have hD : D (appₗ (Φ (x - y))) = 0 := LinearMap.ext fun p ↦ by
      obtain ⟨m, rfl⟩ := z.surjective p
      exact h0 m
    have happ : appₗ (Φ (x - y)) = 0 := D.injective (hD.trans D.map_zero.symm)
    have hΦ : Φ (x - y) = 0 := Modules.hom_ext_of_isAffine fun m ↦ congr($happ m)
    rw [← sub_eq_zero]
    exact Φ.injective (hΦ.trans Φ.map_zero.symm)
  · let l' : Module.Dual k Γ(ℱ, ⊤) :=
      { toFun p := l (z.symm p)
        map_add' p q := by rw [map_add, map_add]
        map_smul' c p := by
          have : z.symm (c • p) = c • z.symm p := by
            apply z.injective
            rw [hz, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          rw [this, map_smul, RingHom.id_apply, smul_eq_mul] }
    have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := X.ringCatSheaf)
    obtain ⟨φ, hφ⟩ := Modules.exists_hom_app_top_eq_of_isAffine (M := ℱ)
      (N := SheafOfModules.unit X.ringCatSheaf) (D.symm l')
    refine ⟨Φ.symm φ, LinearMap.ext fun m ↦ ?_⟩
    change Algebra.trace k Γ(X, ⊤) ((Φ (Φ.symm φ)).app ⊤ (z m)) = l m
    rw [AddEquiv.apply_symm_apply, hφ]
    exact congr($(D.apply_symm_apply l') (z m)).trans (congrArg l (z.symm_apply_apply m))

/-- **Serre duality in dimension `0`.** Let `X` be smooth and proper of relative dimension `0`
over `k`, i.e. `X = Spec A` with `A` finite étale over `k`, so that the canonical module is
`ω_X = 𝒪_X`. Then `ℱ ↦ H^0(X, ℱ)^∨` and `ℱ ↦ H^0(X, ℱᵛ)` are naturally isomorphic as
contravariant functors on finite locally free `ℱ`: there are `k`-linear isomorphisms
`e ℱ : H^0(X, ℱ)^∨ ≅ H^0(X, ℱᵛ)` such that for every morphism `φ : ℱ ⟶ 𝒢` of finite locally
free modules the square
```
  H^0(𝒢)^∨ ───── e 𝒢 ─────▶ H^0(𝒢ᵛ)
     │                         │
 H^0(φ)^∨                   H^0(φᵛ)
     ▼                         ▼
  H^0(ℱ)^∨ ───── e ℱ ─────▶ H^0(ℱᵛ)
```
commutes. The isomorphism is the one induced by the trace pairing
`H^0(ℱ) ⊗ H^0(ℱᵛ) → H^0(𝒪_X) = A → k`, whose last map is the trace `Tr_{A/k}`. In degrees
`q > 0` both sides vanish.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem serreDuality_zero [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        Modules.cohomologyFunctor k 0) := by
  have : Etale (X ↘ Spec (.of k)) := (Etale.iff_smoothOfRelativeDimension_zero _).2 ‹_›
  have : IsFinite (X ↘ Spec (.of k)) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  have hX : (globalSectionsRingHom k (X := X)).Etale := by
    have h := (HasRingHomProperty.iff_of_isAffine (P := @Etale)
      (f := X ↘ Spec (.of k))).mp inferInstance
    rw [globalSectionsRingHom, CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) h
  have he (ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory) :=
    have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
    have : ℱ.obj.IsQuasicoherent := inferInstance
    exists_linearEquiv_dual_H_zero_of_etale hX ℱ.obj
  choose e he using he
  refine ⟨(NatIso.ofComponents (fun ℱ ↦ (e ℱ.unop).toModuleIso) fun {ℱ 𝒢} f ↦ ?_).symm⟩
  ext x
  refine LinearMap.ext fun m ↦ ?_
  change e 𝒢.unop (Modules.H.map (Modules.dualMap f.unop.hom) 0 x) m =
    e ℱ.unop x (Modules.H.map f.unop.hom 0 m)
  let := (globalSectionsRingHom k (X := X)).toAlgebra
  refine (he 𝒢.unop _ m).trans (Eq.trans (congrArg (Algebra.trace k Γ(X, ⊤)) ?_)
    (he ℱ.unop x _).symm)
  have h := Modules.homObjHZeroAddEquiv_map (N := SheafOfModules.unit X.ringCatSheaf)
    f.unop.hom x
  rw [Modules.H.zeroLinearEquiv_map]
  exact congr(Modules.Hom.app $h ⊤ (Modules.H.zeroLinearEquiv 𝒢.unop.obj m))

/-- **Serre duality in dimension `0`, with the trace formula.** Let `X` be smooth and proper of
relative dimension `0` over `k`, so `X = Spec A` with `A = Γ(X, ⊤)` finite étale over `k`. There
is an isomorphism `e : (ℱ ↦ H^0(X, ℱ)^∨) ≅ (ℱ ↦ H^0(X, ℱᵛ))` of contravariant functors on finite
locally free `ℱ` whose inverse is the trace pairing: a global section `x` of `ℱᵛ`, i.e. a
morphism `ℱ ⟶ 𝒪_X`, is sent to the functional `m ↦ Tr_{A/k}(x(m))` on `H^0(X, ℱ)`. That is,
the duality morphism `t_X : H^0(X, 𝒪_X) = A → k` is the trace `Tr_{A/k}`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, case `n = 0`) -/
theorem exists_serreDuality_zero_iso_trace [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    ∃ e : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        Modules.cohomologyFunctor k 0,
      ∀ (ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ)
        (x : Modules.H (ℱ.unop.obj : X.Modules)ᵛ 0)
        (m : Modules.H (ℱ.unop.obj : X.Modules) 0),
        DFunLike.coe (F := Module.Dual k (Modules.H (ℱ.unop.obj : X.Modules) 0))
          ((e.inv.app ℱ).hom x) m =
        Algebra.trace k Γ(X, ⊤) ((Modules.homObjHZeroAddEquiv ℱ.unop.obj
          (SheafOfModules.unit _) x).app ⊤ (Modules.H.zeroLinearEquiv ℱ.unop.obj m)) := by
  have : Etale (X ↘ Spec (.of k)) := (Etale.iff_smoothOfRelativeDimension_zero _).2 ‹_›
  have : IsFinite (X ↘ Spec (.of k)) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  have hX : (globalSectionsRingHom k (X := X)).Etale := by
    have h := (HasRingHomProperty.iff_of_isAffine (P := @Etale)
      (f := X ↘ Spec (.of k))).mp inferInstance
    rw [globalSectionsRingHom, CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) h
  have he (ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory) :=
    have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
    have : ℱ.obj.IsQuasicoherent := inferInstance
    exists_linearEquiv_dual_H_zero_of_etale hX ℱ.obj
  choose e he using he
  refine ⟨(NatIso.ofComponents (fun ℱ ↦ (e ℱ.unop).toModuleIso) fun {ℱ 𝒢} f ↦ ?_).symm,
    fun ℱ x m ↦ ?_⟩
  · ext x
    refine LinearMap.ext fun m ↦ ?_
    change e 𝒢.unop (Modules.H.map (Modules.dualMap f.unop.hom) 0 x) m =
      e ℱ.unop x (Modules.H.map f.unop.hom 0 m)
    let := (globalSectionsRingHom k (X := X)).toAlgebra
    refine (he 𝒢.unop _ m).trans (Eq.trans (congrArg (Algebra.trace k Γ(X, ⊤)) ?_)
      (he ℱ.unop x _).symm)
    have h := Modules.homObjHZeroAddEquiv_map (N := SheafOfModules.unit X.ringCatSheaf)
      f.unop.hom x
    rw [Modules.H.zeroLinearEquiv_map]
    exact congr(Modules.Hom.app $h ⊤ (Modules.H.zeroLinearEquiv 𝒢.unop.obj m))
  · exact he ℱ.unop x m

/-- **Serre duality in dimension `0`, positive degrees.** Let `X` be smooth and proper of
relative dimension `0` over `k`, so `X` is affine (finite étale over `k`). Then for every finite
locally free `ℱ` and every `q > 0`, both sides of Serre duality vanish:
`H^q(X, ℱ) = 0` and `H^q(X, ℱᵛ) = 0` (here `ω_X = 𝒪_X`, so `ℱᵛ ⊗ ω_X ≅ ℱᵛ`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, case `n = 0`) -/
theorem subsingleton_H_and_dual_of_smoothOfRelativeDimension_zero
    [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] {q : ℕ} (hq : 0 < q) :
    Subsingleton (ℱ.H q) ∧ Subsingleton (ℱᵛ.H q) := by
  have : Etale (X ↘ Spec (.of k)) := (Etale.iff_smoothOfRelativeDimension_zero _).2 ‹_›
  have : IsFinite (X ↘ Spec (.of k)) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  have : ℱᵛ.IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual ℱ
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  exact ⟨Modules.subsingleton_H_succ_of_isAffine ℱ q,
    Modules.subsingleton_H_succ_of_isAffine ℱᵛ q⟩

/-- **`h⁰(Ω¹) = h¹(𝒪_X)`.** On a smooth proper curve over `k`,
`dim_k H⁰(X, Ω¹_{X/k}) = dim_k H¹(X, 𝒪_X)`. -/
theorem finrankH_relativeDifferentials_zero_eq_arithmeticGenus
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 0 = arithmeticGenus k X := by
  -- Serre duality for `ℱ = 𝒪_X` and `q = 1`, with `𝒪_Xᵛ ⊗ Ω¹ ≅ Ω¹`.
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  obtain ⟨d⟩ := Modules.nonempty_dual_unit_iso (X := X)
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  let 𝒪 : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf,
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) 𝒪.obj 1)) =
      Modules.finrankH k (𝒪.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    (e.app (op 𝒪)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  rw [← Modules.finrankH_congr k (whiskerRightIso d _ ≪≫ λ_ _) 0, ← h]
  rfl

/-- **The two genera agree.** On a smooth proper curve over `k`, the genus
`dim_k Γ(X, Ω¹_{X/k})` of `def-sc-curves` is the arithmetic genus `dim_k H¹(X, 𝒪_X)`, the genus
of blueprint `def-pc-genus`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`,
`theorem-riemann-roch-coherent-serre-duality--6`) -/
theorem genus_eq_arithmeticGenus [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    (X ↘ Spec (.of k)).genus = arithmeticGenus k X := by
  rw [Hom.genus_eq_finrankH_zero, finrankH_relativeDifferentials_zero_eq_arithmeticGenus]

/-- Blueprint `prose-C-05`: The genus of a curve.

The genus of a smooth proper curve `X` over `k` is finite: `H⁰(X, Ω¹_{X/k})`, whose dimension is
the genus (`AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_zero`), is a finite-dimensional
`k`-vector space, since `Ω¹_{X/k}` is invertible and the cohomology of a coherent module on a
proper scheme over a field is finite-dimensional (Stacks 02O5). -/
theorem finiteDimensional_H_relativeDifferentials
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (q : ℕ) :
    FiniteDimensional k ((X ↘ Spec (.of k)).relativeDifferentials.H q) :=
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  inferInstance

end Duality

section PointIdeal

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)

/-- Away from the image of a rational point `x`, the ideal sheaf `ker x` is everything. -/
lemma Hom.ideal_ker_eq_top_of_notMem (W : X.affineOpens) (h : x.base default ∉ W.1) :
    x.ker.ideal W = ⊤ := by
  have hW : x ⁻¹ᵁ W.1 = ⊥ := by
    refine eq_bot_iff.mpr fun y hy ↦ (h ?_).elim
    rw [Subsingleton.elim y default] at hy
    exact hy
  have : Subsingleton Γ(Spec (.of k), x ⁻¹ᵁ W.1) := by
    rw [hW]
    infer_instance
  rw [Hom.ker_apply, Ideal.eq_top_iff_one, RingHom.mem_ker]
  exact Subsingleton.elim _ _

/-- Near the image `P` of a rational point `x`, a function lies in the ideal sheaf `ker x` if
and only if it vanishes at `P`. -/
lemma Hom.mem_ideal_ker_iff (W : X.affineOpens) (h : x.base default ∈ W.1) (c : Γ(X, W.1)) :
    c ∈ x.ker.ideal W ↔ x.base default ∉ X.basicOpen c := by
  have e : (⊤ : (Spec (.of k)).Opens) ≤ x ⁻¹ᵁ W.1 := fun y _ ↦ by
    rw [Subsingleton.elim y default]
    exact h
  rw [Hom.ker_apply, RingHom.mem_ker]
  have h1 : x.app W.1 c = 0 ↔ x.appLE W.1 ⊤ e c = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    have hinj : Function.Injective ((Spec (.of k)).presheaf.map (homOfLE e).op) := by
      have : IsIso (homOfLE e).op := by
        have : x ⁻¹ᵁ W.1 = ⊤ := top_le_iff.mp e
        rw [show (homOfLE e).op = (eqToHom (by rw [this])) from Subsingleton.elim _ _]
        infer_instance
      exact (ConcreteCategory.bijective_of_isIso _).1
    exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦ hinj (h.trans (map_zero _).symm)⟩
  have h2 : x.base default ∈ X.basicOpen c ↔
      default ∈ (Spec (.of k)).basicOpen (x.appLE W.1 ⊤ e c) := by
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩
  rw [h1, h2, basicOpen_eq_of_affine', PrimeSpectrum.mem_basicOpen, not_not]
  have hbot (p : PrimeSpectrum k) : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hbot, Ideal.mem_bot]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of k)).hom).1).symm

/-- The ideal sheaf of a rational point `x` generates the maximal ideal of the local ring at its
image. -/
lemma Hom.map_germ_ideal_ker (W : X.affineOpens) (h : x.base default ∈ W.1) :
    (x.ker.ideal W).map (X.presheaf.germ W.1 (x.base default) h).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (x.base default)) := by
  let : Algebra Γ(X, W.1) (X.presheaf.stalk (x.base default)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x.base default, h⟩
  have := W.2.isLocalization_stalk ⟨x.base default, h⟩
  have e : x.ker.ideal W = (W.2.primeIdealOf ⟨x.base default, h⟩).asIdeal := by
    ext c
    rw [x.mem_ideal_ker_iff W h c, Scheme.mem_basicOpen _ _ _ h, ← mem_nonunits_iff,
      ← IsLocalRing.mem_maximalIdeal]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (x.base default))
      (W.2.primeIdealOf ⟨x.base default, h⟩).asIdeal c
  rw [e]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

end PointIdeal

section ClosedPoint

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Over an algebraically closed field, every closed point of a scheme locally of finite type is
the image of a rational point. -/
lemma Hom.exists_fieldPoints_base_eq_of_isClosed [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {P : X} (hP : IsClosed {P}) :
    ∃ x : f.fieldPoints k, x.1.base default = P := by
  rw [Hom.exists_fieldPoints_base_eq_iff]
  let := (f.residueFieldAlgebraMap P).toAlgebra
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : Module.Finite k (X.residueField P) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hP
    have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
      (f := X.fromSpecResidueField P ≫ f)).mpr inferInstance
    rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff] at this
    exact this
  have hb := IsAlgClosed.ringHom_bijective_of_isIntegral (f.residueFieldAlgebraMap P)
    (RingHom.IsIntegral.of_finite (RingHom.finite_algebraMap.mpr inferInstance))
  let e := RingEquiv.ofBijective _ hb
  refine ⟨CommRingCat.ofHom e.symm.toRingHom, ?_⟩
  ext c
  exact e.symm_apply_apply c

/-- The image of a rational point of a scheme locally of finite type over a field is closed. -/
lemma Hom.isClosed_singleton_fieldPoints (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : f.fieldPoints k) : IsClosed {x.1.base default} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hx : x.1 ≫ f = 𝟙 _ := by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have : LocallyOfFiniteType x.1 := by
    have : LocallyOfFiniteType (x.1 ≫ f) := by rw [hx]; infer_instance
    exact locallyOfFiniteType_of_comp x.1 f
  exact x.1.closedPoints_subset_preimage_closedPoints
    (show IsClosed {default} from isClosed_discrete _)

end ClosedPoint

section VeryAmpleCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- **A section vanishing at a rational point vanishes on it.** A global section `σ` of an
invertible `N` which does not generate `N` at the image of a rational point `x` maps to zero in
`N ⧸ 𝒪_X(-x) N`. -/
lemma Modules.app_cokernel_π_eq_zero_of_not_generatesAt (N : X.Modules) [N.IsInvertible]
    (x : (X ↘ Spec (.of k)).fieldPoints k) (σ : Γ(N, ⊤))
    (hσ : ¬ Modules.GeneratesAt σ (x.1.base default)) :
    ((λ_ N).inv ≫ cokernel.π (x.1.ker.toModulesι ▷ N)).app ⊤ σ = 0 := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible N
  have hP := (X ↘ Spec (.of k)).isClosed_singleton_fieldPoints x
  refine Modules.app_cokernel_π_eq_zero _ _ σ fun y ↦ ?_
  by_cases hy : y = x.1.base default
  · subst hy
    obtain ⟨W, hxW, -, e, he⟩ := Modules.exists_isFreeGenerator N
      (TopologicalSpace.Opens.mem_top (x.1.base default))
    obtain ⟨c, hc⟩ := he.exists_smul_eq (N.presheaf.map (homOfLE le_top).op σ)
    refine ⟨W, hxW, e, c, (x.1.mem_ideal_ker_iff W hxW c).mpr fun h ↦ hσ ?_, hc.symm⟩
    exact Modules.generatesAt_of_mem_basicOpen he hc.symm h
  · obtain ⟨W, hyW, hWP, e, he⟩ := Modules.exists_isFreeGenerator N
      (W := ⟨_, hP.isOpen_compl⟩) (x := y) hy
    obtain ⟨c, hc⟩ := he.exists_smul_eq (N.presheaf.map (homOfLE le_top).op σ)
    refine ⟨W, hyW, e, c, ?_, hc.symm⟩
    rw [x.1.ideal_ker_eq_top_of_notMem W fun h ↦ hWP h rfl]
    trivial

/-- **Twisting by a rational point at which `h⁰` drops.** If `h⁰(N ⊗ 𝒪_X(-x)) + 1 = h⁰(N)`
for an invertible `N` and a rational point `x`, some global section of `N` has non-zero image in
`N ⧸ 𝒪_X(-x) N`. -/
lemma Modules.exists_app_cokernel_π_ne_zero (N : X.Modules) [N.IsInvertible]
    (x : (X ↘ Spec (.of k)).fieldPoints k)
    (h : Modules.finrankH k (N ⊗ x.1.ker.toModules) 0 + 1 = Modules.finrankH k N 0) :
    ∃ σ : Γ(N, ⊤), ((λ_ N).inv ≫ cokernel.π (x.1.ker.toModulesι ▷ N)).app ⊤ σ ≠ 0 := by
  have hJ := Hom.isInvertible_ker_fieldPoints x
  have := hJ.isInvertible_toModules
  let S := ShortComplex.mk (x.1.ker.toModulesι ▷ N) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have : S.X₂.IsInvertible := Modules.IsInvertible.of_iso (λ_ N).symm
  have := hJ.finiteDimensional_H_cokernel_whiskerRight (k := k) N 0
  have : FiniteDimensional k (S.X₂.H 0) := Modules.finiteDimensional_H (M := S.X₂) k 0
  have h3 : Modules.finrankH k S.X₃ 0 = 1 := by
    have := hJ.subsingleton_H_one_cokernel_whiskerRight k N
    have h := hJ.eulerChar_cokernel_whiskerRight (k := k) N
    have h1 : Modules.finrankH k (cokernel (x.1.ker.toModulesι ▷ N)) 1 = 0 :=
      Module.finrank_zero_of_subsingleton
    have := x.1.ker.isQuasicoherent_cokernel_whiskerRight N
    rw [Hom.finrankΓ_subschemeι_ker_fieldPoints,
      Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, h1] at h
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one, Nat.cast_eq_one] at h
    exact h
  let f := Modules.H.mapLinearMap k S.f 0
  let g := Modules.H.mapLinearMap k S.g 0
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Modules.H.injective_map_zero_of_shortExact hS)
  have hg : LinearMap.ker g = LinearMap.range f := by
    ext y
    exact SetLike.ext_iff.mp (Modules.H.ker_map_g_eq_range_map_f hS 0) y
  have hrf : Module.finrank k (LinearMap.range f) = Modules.finrankH k S.X₁ 0 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hf, finrank_bot] at this
    exact this.trans rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  rw [hg, hrf] at h2
  have e₁ : S.X₁ ≅ N ⊗ x.1.ker.toModules := β_ _ _
  have e₂ : S.X₂ ≅ N := λ_ N
  rw [Modules.finrankH_congr k e₁] at h2
  change _ + _ = Modules.finrankH k S.X₂ 0 at h2
  rw [Modules.finrankH_congr k e₂] at h2
  have hpos : LinearMap.range g ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h2
    omega
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  refine ⟨(λ_ N).hom.app ⊤ (Modules.H.zeroLinearEquiv S.X₂ z), fun h0 ↦ hz ?_⟩
  rw [Hom.comp_app, ConcreteCategory.comp_apply, Modules.inv_app_hom_app_apply_of_iso] at h0
  apply (Modules.H.zeroLinearEquiv S.X₃).injective
  rw [map_zero, Modules.H.mapLinearMap_apply, Modules.H.zeroLinearEquiv_map]
  exact h0

/-- **Base point freeness.** If `h⁰(ℳ ⊗ 𝒪_X(-x)) + 1 = h⁰(ℳ)` and the global sections `s j`
span `Γ(X, ℳ)`, then some `s j` generates `ℳ` at `x`. -/
lemma Modules.exists_generatesAt_of_finrankH {n : Type*} (ℳ : X.Modules) [ℳ.IsInvertible]
    (s : n → Γ(ℳ, ⊤)) (hspan : ∀ σ : Γ(ℳ, ⊤), σ ∈ Submodule.span Γ(X, ⊤) (Set.range s))
    (x : (X ↘ Spec (.of k)).fieldPoints k)
    (h₁ : Modules.finrankH k (ℳ ⊗ x.1.ker.toModules) 0 + 1 = Modules.finrankH k ℳ 0) :
    ∃ j, Modules.GeneratesAt (s j) (x.1.base default) := by
  obtain ⟨σ, hσ⟩ := Modules.exists_app_cokernel_π_ne_zero ℳ x h₁
  by_contra! hs
  have key (τ : Γ(ℳ, ⊤)) (hτ : τ ∈ Submodule.span Γ(X, ⊤) (Set.range s)) :
      ((λ_ ℳ).inv ≫ cokernel.π (x.1.ker.toModulesι ▷ ℳ)).app ⊤ τ = 0 := by
    induction hτ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Modules.app_cokernel_π_eq_zero_of_not_generatesAt ℳ x _ (hs j)
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [Hom.app_smul, ha, smul_zero]
  exact hσ (key σ (hspan σ))

/-- The setting of the two-point conditions: a global section of `𝒪_X(-x) ⊗ ℳ` which
generates at `y`. -/
lemma Modules.exists_generatesAt_tensorObj_toModules_ker (ℳ : X.Modules) [ℳ.IsInvertible]
    (x y : (X ↘ Spec (.of k)).fieldPoints k)
    (h₁ : Modules.finrankH k (ℳ ⊗ x.1.ker.toModules) 0 + 1 = Modules.finrankH k ℳ 0)
    (h₂ : Modules.finrankH k ((ℳ ⊗ x.1.ker.toModules) ⊗ y.1.ker.toModules) 0 + 2 =
      Modules.finrankH k ℳ 0) :
    ∃ σ : Γ(x.1.ker.toModules ⊗ ℳ, ⊤), Modules.GeneratesAt σ (y.1.base default) := by
  have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
  have hdim : Modules.finrankH k ((x.1.ker.toModules ⊗ ℳ) ⊗ y.1.ker.toModules) 0 + 1 =
      Modules.finrankH k (x.1.ker.toModules ⊗ ℳ) 0 := by
    rw [Modules.finrankH_congr k (β_ x.1.ker.toModules ℳ),
      Modules.finrankH_congr k (whiskerRightIso (β_ x.1.ker.toModules ℳ) _)]
    omega
  obtain ⟨σ, hσ⟩ := Modules.exists_app_cokernel_π_ne_zero _ y hdim
  refine ⟨σ, ?_⟩
  by_contra h
  exact hσ (Modules.app_cokernel_π_eq_zero_of_not_generatesAt _ y σ h)

/-- **Separating points.** Under the two-point conditions at `x ≠ y`, some global section of `ℳ`
vanishes at `x` but generates `ℳ` at `y`. -/
lemma Modules.exists_not_generatesAt_generatesAt (ℳ : X.Modules) [ℳ.IsInvertible]
    (x y : (X ↘ Spec (.of k)).fieldPoints k) (hxy : x.1.base default ≠ y.1.base default)
    (h₁ : Modules.finrankH k (ℳ ⊗ x.1.ker.toModules) 0 + 1 = Modules.finrankH k ℳ 0)
    (h₂ : Modules.finrankH k ((ℳ ⊗ x.1.ker.toModules) ⊗ y.1.ker.toModules) 0 + 2 =
      Modules.finrankH k ℳ 0) :
    ∃ t : Γ(ℳ, ⊤), ¬ Modules.GeneratesAt t (x.1.base default) ∧
      Modules.GeneratesAt t (y.1.base default) := by
  have hI := Hom.isInvertible_ker_fieldPoints x
  have hP := (X ↘ Spec (.of k)).isClosed_singleton_fieldPoints x
  obtain ⟨σ, hσ⟩ := Modules.exists_generatesAt_tensorObj_toModules_ker ℳ x y h₁ h₂
  refine ⟨(x.1.ker.toModulesι ▷ ℳ ≫ (λ_ ℳ).hom).app ⊤ σ, fun hgen ↦ ?_, ?_⟩
  · obtain ⟨W, hPW, -, e, v, π, he, hspan, ht, -⟩ :=
      Modules.exists_app_leftUnitor_whiskerRight_toModulesι x.1.ker ℳ hI σ
        (TopologicalSpace.Opens.mem_top (x.1.base default))
    have h1 := Modules.mem_basicOpen_of_generatesAt he ht hPW hgen
    rw [Scheme.basicOpen_mul] at h1
    have hπ : π ∈ x.1.ker.ideal W := hspan ▸ Ideal.mem_span_singleton_self π
    exact (x.1.mem_ideal_ker_iff W hPW π).mp hπ h1.2
  · obtain ⟨W, hQW, hWO, e, v, π, he, hspan, ht, hv⟩ :=
      Modules.exists_app_leftUnitor_whiskerRight_toModulesι x.1.ker ℳ hI σ
        (O := ⟨_, hP.isOpen_compl⟩) (x := y.1.base default) (Ne.symm hxy)
    rw [x.1.ideal_ker_eq_top_of_notMem W fun h ↦ hWO h rfl, Ideal.span_singleton_eq_top] at hspan
    refine Modules.generatesAt_of_mem_basicOpen he ht ?_
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hspan]
    exact ⟨hv hσ, hQW⟩

/-- **Separating tangent vectors.** Under the two-point condition at `x = y`, some global
section of `ℳ` is, near `x`, a multiple `c • e` of a free generator `e` by a function `c`
generating the ideal of `x`. -/
lemma Modules.exists_span_eq_ideal_ker (ℳ : X.Modules) [ℳ.IsInvertible]
    (x : (X ↘ Spec (.of k)).fieldPoints k)
    (h₁ : Modules.finrankH k (ℳ ⊗ x.1.ker.toModules) 0 + 1 = Modules.finrankH k ℳ 0)
    (h₂ : Modules.finrankH k ((ℳ ⊗ x.1.ker.toModules) ⊗ x.1.ker.toModules) 0 + 2 =
      Modules.finrankH k ℳ 0) :
    ∃ t : Γ(ℳ, ⊤), ∃ W : X.affineOpens, x.1.base default ∈ W.1 ∧
      ∃ (e : Γ(ℳ, W.1)) (c : Γ(X, W.1)), Modules.IsFreeGenerator e ∧
        ℳ.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op t = c • e ∧
        Ideal.span {c} = x.1.ker.ideal W := by
  have hI := Hom.isInvertible_ker_fieldPoints x
  obtain ⟨σ, hσ⟩ := Modules.exists_generatesAt_tensorObj_toModules_ker ℳ x x h₁ h₂
  obtain ⟨W, hPW, -, e, v, π, he, hspan, ht, hv⟩ :=
    Modules.exists_app_leftUnitor_whiskerRight_toModulesι x.1.ker ℳ hI σ
      (TopologicalSpace.Opens.mem_top (x.1.base default))
  have hle : X.basicOpen v ≤ W.1 := X.basicOpen_le v
  let W' : X.affineOpens := ⟨X.basicOpen v, W.2.basicOpen v⟩
  have hu : IsUnit (X.presheaf.map (homOfLE hle).op v) := X.toRingedSpace.isUnit_res_basicOpen v
  refine ⟨(x.1.ker.toModulesι ▷ ℳ ≫ (λ_ ℳ).hom).app ⊤ σ, W', hv hσ,
    ℳ.presheaf.map (homOfLE hle).op e,
    X.presheaf.map (homOfLE hle).op (v * π), he.map hle, ?_, ?_⟩
  · rw [← Modules.presheaf_map_homOfLE_map_homOfLE (le_top : W.1 ≤ ⊤) hle, ht, Modules.map_smul]
  · rw [map_mul, Ideal.span_singleton_mul_left_unit hu, ← x.1.ker.map_ideal (U := W') (V := W)
      hle, ← hspan, Ideal.map_span, Set.image_singleton]
    rfl

end VeryAmpleCurve

section VeryAmpleSpan

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

private lemma appLE_eq_of_eq' {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- For a morphism `φ : X ⟶ ℙ(n; k)` with `φ^* 𝒪(1) ≅ ℳ` sending `φ^* Tⱼ` to `s j`, every
global section in the span of the `s j` is, on the preimage of `D₊(Tᵢ)`, the pullback of a
function on `D₊(Tᵢ)` times `s i`. -/
lemma exists_eq_app_smul_of_mem_span [GlobalSectionsBijective k X] {n : Type u} {ℳ : X.Modules}
    {s : n → Γ(ℳ, ⊤)} {φ : X ⟶ ℙ(n; Spec (.of k))}
    (hφ : φ ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k))
    (ε : ProjectiveSpace.twistRestrict φ 1 ⟶ ℳ) [IsIso ε]
    (hε : ∀ j, ε.app _ (Modules.pullbackSection φ (ProjectiveSpace.twistOneSection n _ j)) =
      ℳ.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j))
    (i : n) {σ : Γ(ℳ, ⊤)} (hσ : σ ∈ Submodule.span Γ(X, ⊤) (Set.range s)) :
    ∃ a : Γ(ℙ(n; Spec (.of k)), ProjectiveSpace.standardOpen n _ i),
      ℳ.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i ≤ ⊤)).op σ =
        φ.app _ a • ℳ.presheaf.map
          (homOfLE (le_top : φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i ≤ ⊤)).op (s i) := by
  induction hσ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨_, ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso ε hε i j⟩
  | zero => exact ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, ha', hb', map_add, add_smul]⟩
  | smul r a _ ha =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨c, rfl⟩ := (GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k)).2 r
    refine ⟨(ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appLE ⊤ _ le_top
      ((Scheme.ΓSpecIso (.of k)).inv c) * a', ?_⟩
    rw [Modules.map_smul, ha', map_mul, mul_smul]
    congr 1
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq' hφ]
    rfl

end VeryAmpleSpan

section LargeDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **The degree of the canonical module.** `deg Ω¹_{X/k} = 2g - 2` on a smooth proper curve
with `H⁰(X, 𝒪_X) = k`, of genus `g`: Serre duality gives `h⁰(Ω¹) = g`
(`AlgebraicGeometry.Scheme.finrankH_relativeDifferentials_zero_eq_arithmeticGenus`) and
`h¹(Ω¹) = h⁰(𝒪_X) = 1`, so `χ(Ω¹) - χ(𝒪_X) = (g - 1) - (1 - g)`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem degree_relativeDifferentials [GlobalSectionsBijective k X] :
    (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 := by
  -- Serre duality for `ℱ = 𝒪_X` and `q = 0`, with `𝒪_Xᵛ ⊗ Ω¹ ≅ Ω¹`.
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 1 0 rfl
  obtain ⟨d⟩ := Modules.nonempty_dual_unit_iso (X := X)
  have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  let 𝒪 : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf,
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) (show X.Modules from 𝒪.obj) 0)) =
      Modules.finrankH k (𝒪.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 1 :=
    (e.app (op 𝒪)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  have h1 : Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 1 = 1 := by
    rw [← Modules.finrankH_congr k (whiskerRightIso d _ ≪≫ λ_ _) 1, ← h]
    exact Modules.finrankH_unit_zero
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (X ↘ Spec (.of k)).relativeDifferentials :=
    Modules.IsInvertible.isQuasicoherent _
  rw [Modules.degree, Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one,
    finrankH_relativeDifferentials_zero_eq_arithmeticGenus, h1, eulerChar_unit_eq]
  push_cast
  ring

/-- **A line bundle of negative degree has no sections.** On a smooth proper curve with
`H⁰(X, 𝒪_X) = k`, an invertible `ℳ` with `deg ℳ < 0` has `H⁰(X, ℳ) = 0`: a nonzero section `s`
would give `ℳ ≅ 𝒪_X(div s)` with `div s` effective, of degree `≥ 0`.

The hypothesis `H⁰(X, 𝒪_X) = k`, which makes `X` connected, cannot be dropped: on
`X = ℙ¹ ⊔ ℙ¹` the line bundle `𝒪(1) ⊔ 𝒪(-3)` has degree `-2` and nonzero sections.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--4`) -/
theorem Modules.finrankH_zero_eq_zero_of_degree_neg [GlobalSectionsBijective k X]
    (ℳ : X.Modules) [ℳ.IsInvertible] (hd : ℳ.degree k < 0) : ℳ.finrankH k 0 = 0 := by
  by_contra h0
  have : Nontrivial (ℳ.H 0) :=
    Module.nontrivial_of_finrank_pos (R := k) (show 0 < ℳ.finrankH k 0 by omega)
  obtain ⟨s, hs⟩ := Modules.exists_ne_zero_of_nontrivial_H_zero ℳ
  -- `X` is integral, so the zero scheme of the non-zero section `s` is an effective divisor `D`
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have := IsRegular.of_smooth (X ↘ Spec (.of k))
  have := GlobalSectionsBijective.connectedSpace (k := k) (X := X)
  have := IsRegular.isIntegral X
  have := Modules.IsInvertible.sheafOfModules_isInvertible ℳ
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have hJ : s.zeroLocus.IsInvertible :=
    (Modules.Hom.isLocallyPrincipal_zeroLocus s).isInvertible
      fun h ↦ hs ((Modules.Hom.zeroLocus_eq_bot_iff s).mp h)
  -- `ℳ ≅ 𝒪_X(D)`, of degree `deg D ≥ 0`
  obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj s hJ
  have hD := hJ.degree_dual_toModules (k := k)
  rw [Modules.degree_congr k (e ≪≫ ρ_ _)] at hd
  omega

/-- **`h¹` of a line bundle of large degree vanishes.** A line bundle `ℒ` of degree
`d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has `H¹(X, ℒ) = 0`:
by Serre duality `H¹(ℒ)^∨ ≅ H⁰(ℒᵛ ⊗ Ω¹)`, and `ℒᵛ ⊗ Ω¹` has degree `2g - 2 - d < 0`. -/
theorem Modules.finrankH_one_eq_zero_of_degree [GlobalSectionsBijective k X] (ℒ : X.Modules)
    [ℒ.IsInvertible] (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    ℒ.finrankH k 1 = 0 := by
  have := (X ↘ Spec (.of k)).isInvertible_relativeDifferentials
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  have := Modules.IsInvertible.sheafOfModules_isInvertible ℒ
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  let ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨ℒ, SheafOfModules.IsInvertible.isFiniteLocallyFree ℒ⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) (show X.Modules from ℱ.obj) 1)) =
      Modules.finrankH k (ℱ.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    (e.app (op ℱ)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  refine h.trans (Modules.finrankH_zero_eq_zero_of_degree_neg _ ?_)
  change (ℒᵛ ⊗ₘ (X ↘ Spec (.of k)).relativeDifferentials).degree k < 0
  rw [Modules.degree_tensorObj, Modules.degree_dual, degree_relativeDifferentials]
  linarith

/-- **Riemann–Roch for curves, `h⁰` of a line bundle of large degree.** A line bundle `ℒ` of
degree `d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has
`h^0(ℒ) = d + 1 - g`; equivalently `h^1(ℒ) = 0`
(`AlgebraicGeometry.Scheme.Modules.finrankH_one_eq_zero_of_degree`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem finrankH_zero_eq [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X := by
  rw [Modules.degree, eulerChar_unit_eq, Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one,
    Modules.finrankH_one_eq_zero_of_degree ℒ hd]
  ring

/-- **The criterion for very ampleness on a curve.** Let `k` be algebraically closed and `ℳ` a
line bundle on a smooth proper curve with `H⁰(X, 𝒪_X) = k`. Suppose that twisting by the ideal
sheaf of a rational point lowers `h⁰` by one, and twisting by the ideal sheaves of two rational
points `P` and `Q`, possibly equal, lowers `h⁰` by two. Then `ℳ` is very ample.

Since `k` is algebraically closed, every closed point is rational. The first condition says that
the complete linear system `|ℳ|` is base point free, so it defines a morphism `φ : X ⟶ ℙ^N`. The
second condition with `P ≠ Q` gives a section vanishing at `P` but not at `Q`, so `φ` is
injective, and with `P = Q` a section vanishing to order exactly one at `P`, so `φ` is unramified.
Being proper with finite fibres, `φ` is finite, and a finite morphism which is injective and
unramified, with trivial residue field extensions, is a closed immersion (Nakayama).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, second part of the proof) -/
theorem isVeryAmple_of_finrankH_zero_tensorObj_toModules_ker [IsAlgClosed k]
    [GlobalSectionsBijective k X] (ℳ : X.Modules) [ℳ.IsInvertible]
    (h₁ : ∀ x : (X ↘ Spec (.of k)).fieldPoints k,
      Modules.finrankH k (ℳ ⊗ x.1.ker.toModules) 0 + 1 = ℳ.finrankH k 0)
    (h₂ : ∀ x y : (X ↘ Spec (.of k)).fieldPoints k,
      Modules.finrankH k ((ℳ ⊗ x.1.ker.toModules) ⊗ y.1.ker.toModules) 0 + 2 =
        ℳ.finrankH k 0) :
    IsVeryAmple (X ↘ Spec (.of k)) ℳ := by
  have : FiniteDimensional k (ℳ.H 0) := Modules.finiteDimensional_H (M := ℳ) k 0
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  -- a basis `s` of the global sections
  let b := Module.finBasis k (ℳ.H 0)
  let n := ULift.{u} (Fin (Module.finrank k (ℳ.H 0)))
  let s : n → Γ(ℳ, ⊤) := fun j ↦ Modules.H.zeroLinearEquiv ℳ (b j.down)
  have hspan (σ : Γ(ℳ, ⊤)) : σ ∈ Submodule.span Γ(X, ⊤) (Set.range s) := by
    obtain ⟨z, rfl⟩ := (Modules.H.zeroLinearEquiv ℳ).surjective σ
    rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [Modules.smul_H_eq_globalSectionsRingHom_smul, LinearEquiv.map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j⟩, rfl⟩)
  have hpt (P : X) (hP : IsClosed {P}) :
      ∃ x : (X ↘ Spec (.of k)).fieldPoints k, x.1.base default = P :=
    (X ↘ Spec (.of k)).exists_fieldPoints_base_eq_of_isClosed hP
  -- the loci where the `s j` generate `ℳ` cover `X`
  have hU : ⨆ j, Modules.generatingLocus (s j) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPZ, hPcl⟩ := (⨆ j, Modules.generatingLocus (s j)).isOpen.isClosed_compl
      |>.exists_closed_singleton (by
        rw [Set.nonempty_compl]
        exact fun h ↦ hne (SetLike.coe_injective h))
    obtain ⟨x, rfl⟩ := hpt P hPcl
    obtain ⟨j, hj⟩ := Modules.exists_generatesAt_of_finrankH ℳ s hspan x (h₁ x)
    exact hPZ (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩)
  obtain ⟨φ, hφ, ε, hεi, hε⟩ := ProjectiveSpace.exists_hom_twistRestrict
    (g := X ↘ Spec (.of k)) (s := s) (U := fun j ↦ Modules.generatingLocus (s j))
    (hs := fun j ↦ Modules.isFreeGenerator_generatingLocus (s j)) hU
  refine ⟨n, φ, inferInstance, ?_, hφ, ⟨asIso ε⟩⟩
  have : IsProper φ := by
    have : IsProper (φ ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k)) := by rw [hφ]; infer_instance
    exact IsProper.of_comp φ (ℙ(n; Spec (.of k)) ↘ Spec (.of k))
  have hcov (P : X) : ∃ i, P ∈ φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i := by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen n _).ge (Set.mem_univ (φ P)))
    exact ⟨i, hi⟩
  refine isClosedImmersion_of_injective_of_le_map_maximalIdeal φ (X ↘ Spec (.of k))
    (ℙ(n; Spec (.of k)) ↘ Spec (.of k)) hφ ?_ ?_
  · intro P Q hPcl hQcl hPQ
    by_contra hne
    obtain ⟨x, rfl⟩ := hpt P hPcl
    obtain ⟨y, rfl⟩ := hpt Q hQcl
    obtain ⟨t, htP, htQ⟩ :=
      Modules.exists_not_generatesAt_generatesAt ℳ x y hne (h₁ x) (h₂ x y)
    obtain ⟨i, hi⟩ := hcov (y.1.base default)
    obtain ⟨a, ha⟩ := exists_eq_app_smul_of_mem_span hφ ε hε i (hspan t)
    have he := ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso ε hε i
    have h1 := Modules.mem_basicOpen_of_generatesAt he ha hi htQ
    have h2 : x.1.base default ∉ X.basicOpen (φ.app _ a) := fun h ↦
      htP (Modules.generatesAt_of_mem_basicOpen he ha h)
    rw [← Scheme.preimage_basicOpen] at h1 h2
    rw [Scheme.Hom.mem_preimage, ← hPQ, ← Scheme.Hom.mem_preimage] at h1
    exact h2 h1
  · intro P hPcl
    obtain ⟨x, rfl⟩ := hpt P hPcl
    obtain ⟨t, W, hPW, e, c, he, ht, hc⟩ := Modules.exists_span_eq_ideal_ker ℳ x (h₁ x) (h₂ x x)
    obtain ⟨i, hi⟩ := hcov (x.1.base default)
    obtain ⟨a, ha⟩ := exists_eq_app_smul_of_mem_span hφ ε hε i (hspan t)
    have hsi := ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso ε hε i
    have hVW : W.1 ⊓ (φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i) ≤ W.1 := inf_le_left
    have hVi : W.1 ⊓ (φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i) ≤
        (φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i) := inf_le_right
    have hPV : x.1.base default ∈ W.1 ⊓ (φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i) := ⟨hPW, hi⟩
    obtain ⟨w, hw⟩ := (he.map hVW).exists_unit_smul_eq (hsi.map hVi)
    rw [Modules.presheaf_map_homOfLE_map_homOfLE] at hw
    have ht' := congrArg (ℳ.presheaf.map (homOfLE hVW).op) ht
    have ha' := congrArg (ℳ.presheaf.map (homOfLE hVi).op) ha
    simp only [Modules.presheaf_map_homOfLE_map_homOfLE, Modules.map_smul] at ht' ha'
    rw [hw, smul_smul, ht'] at ha'
    have hcV := (he.map hVW).smul_left_injective ha'
    -- germs at `P`
    have hg : X.presheaf.germ W.1 _ hPW c =
        X.presheaf.germ (φ ⁻¹ᵁ ProjectiveSpace.standardOpen n _ i) _ hi (φ.app _ a) *
          X.presheaf.germ _ _ hPV w.1 := by
      rw [← X.presheaf.germ_res_apply (homOfLE hVW) _ hPV, hcV, map_mul,
        X.presheaf.germ_res_apply (homOfLE hVi)]
    have hcmem : c ∈ x.1.ker.ideal W := hc ▸ Ideal.mem_span_singleton_self c
    have hnu : ¬ IsUnit (X.presheaf.germ W.1 _ hPW c) := fun h ↦
      (x.1.mem_ideal_ker_iff W hPW c).mp hcmem ((Scheme.mem_basicOpen _ _ _ hPW).mpr h)
    rw [← x.1.map_germ_ideal_ker W hPW, ← hc, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hg]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← Scheme.Hom.germ_stalkMap_apply]
    refine Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr fun hu ↦ hnu ?_)
    rw [hg, ← Scheme.Hom.germ_stalkMap_apply]
    exact ((hu.map (φ.stalkMap _).hom).mul (w.isUnit.map _))

/-- **A line bundle of degree `≥ 2g + 1` is very ample.** Let `k` be algebraically closed and
`ℳ` a line bundle of degree `d ≥ 2g + 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of
genus `g`. For closed points `P, Q`, Riemann–Roch in degree `≥ 2g - 1`
(`AlgebraicGeometry.Scheme.finrankH_zero_eq`) gives `h⁰(ℳ(-P)) = h⁰(ℳ) - 1` and
`h⁰(ℳ(-P-Q)) = h⁰(ℳ) - 2`: the complete linear system `|ℳ|` is base point free and separates
points and tangent vectors, so it defines a closed immersion into projective space
(`AlgebraicGeometry.Scheme.isVeryAmple_of_finrankH_zero_tensorObj_toModules_ker`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isVeryAmple_of_degree [IsAlgClosed k] [GlobalSectionsBijective k X] (ℳ : X.Modules)
    [ℳ.IsInvertible] (hd : 2 * (arithmeticGenus k X : ℤ) + 1 ≤ ℳ.degree k) :
    IsVeryAmple (X ↘ Spec (.of k)) ℳ := by
  have h₀ := finrankH_zero_eq (k := k) ℳ (by omega)
  refine isVeryAmple_of_finrankH_zero_tensorObj_toModules_ker ℳ (fun x ↦ ?_) fun x y ↦ ?_
  · have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
    have hdx : (ℳ ⊗ x.1.ker.toModules).degree k = ℳ.degree k - 1 := by
      rw [Modules.degree_tensorObj (k := k), degree_toModules_ker_fieldPoints]
      ring
    have h := finrankH_zero_eq (k := k) (ℳ ⊗ x.1.ker.toModules) (by omega)
    omega
  · have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
    have := (Hom.isInvertible_ker_fieldPoints y).isInvertible_toModules
    have hdx : ((ℳ ⊗ x.1.ker.toModules) ⊗ y.1.ker.toModules).degree k = ℳ.degree k - 2 := by
      rw [Modules.degree_tensorObj (k := k), Modules.degree_tensorObj (k := k),
        degree_toModules_ker_fieldPoints,
        degree_toModules_ker_fieldPoints]
      ring
    have h := finrankH_zero_eq (k := k) ((ℳ ⊗ x.1.ker.toModules) ⊗ y.1.ker.toModules)
      (by omega)
    omega

/-- **Positive degree implies ample, over an algebraically closed field.** If `deg ℒ > 0` then
`deg ℒ^{⊗ m} = m deg ℒ ≥ 2g + 1` for `m = 2g + 1`, so `ℒ^{⊗ m}` is very ample
(`AlgebraicGeometry.Scheme.isVeryAmple_of_degree`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isAmple_of_degree_pos_of_isAlgClosed [IsAlgClosed k] [GlobalSectionsBijective k X]
    (ℒ : X.Modules) [ℒ.IsInvertible] (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ := by
  refine ⟨inferInstance, 2 * arithmeticGenus k X + 1, Nat.succ_pos _,
    isVeryAmple_of_degree _ ?_⟩
  rw [Modules.degree_tensorPow]
  push_cast
  nlinarith

/-- **Positive degree implies ample.** An invertible sheaf of positive degree on a smooth
proper curve over `k` with `H⁰(X, 𝒪_X) = k` is ample: after base change to an algebraic closure
`k̄`, where the degree is unchanged (`AlgebraicGeometry.Scheme.Modules.degree_pullback`), some
power `ℒ_{k̄}^{⊗ m}` is very ample
(`AlgebraicGeometry.Scheme.isAmple_of_degree_pos_of_isAlgClosed`), and very ampleness
descends (`AlgebraicGeometry.IsVeryAmple.of_pullback`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality`, part (G)) -/
theorem isAmple_of_degree_pos [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ := by
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : SmoothOfRelativeDimension 1 (Limits.pullback (X ↘ Spec (.of k)) g ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (Limits.pullback (X ↘ Spec (.of k)) g ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  obtain ⟨-, m, hm, hv⟩ := isAmple_of_degree_pos_of_isAlgClosed
    ((Modules.pullback (pullback.fst (X ↘ Spec (.of k)) g)).obj ℒ)
    ((Modules.degree_pullback k K ℒ).symm ▸ hd)
  exact ⟨inferInstance, m, hm, IsVeryAmple.of_pullback _ K _
    (hv.of_iso (Modules.nonempty_pullback_tensorPow_iso _ ℒ m).some.symm)⟩

/-- **Ample if and only if positive degree.** An invertible sheaf on a smooth proper curve over
`k` with `H⁰(X, 𝒪_X) = k` is ample if and only if it has positive degree. Ampleness and degree
are both invariant under base change to an algebraic closure, where an ample line bundle has
positive degree (`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isAmple_iff_degree_pos [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible] :
    IsAmple (X ↘ Spec (.of k)) ℒ ↔ 0 < ℒ.degree k := by
  refine ⟨fun h ↦ ?_, isAmple_of_degree_pos ℒ⟩
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let XK := Limits.pullback (X ↘ Spec (.of k)) g
  have : SmoothOfRelativeDimension 1 (XK ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (XK ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have := GlobalSectionsBijective.nonempty (k := K) (X := XK)
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (XK ↘ Spec (.of K)) 1
  rw [← Modules.degree_pullback k K ℒ]
  have := Scheme.Hom.degree_pos_of_isAmple (XK ↘ Spec (.of K)) (by exact_mod_cast hdim)
    ((Modules.pullback (pullback.fst (X ↘ Spec (.of k)) g)).obj ℒ) (h.pullback_of_field K)
  rwa [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one _ (by exact_mod_cast hdim)]
    at this

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- **Affine complement.** Let `D` be an effective Cartier divisor on a smooth proper curve `X`,
with invertible ideal sheaf `J = 𝒪_X(-D)`, whose line bundle `𝒪_X(D) = J.toModulesᵛ` is ample.
Then `X \ Supp D` is affine. The open complement of the support of `D` is presented by an open
immersion `j` whose range is the complement of the support of `J`. This is the case of curves of
`AlgebraicGeometry.isAffine_compl_of_isAmple_dual_toModules`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`, part (H)) -/
theorem isAffine_compl_of_isAmple {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hample : IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ) {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (hj : Set.range j.base = (J.support : Set X)ᶜ) :
    IsAffine V :=
  isAffine_compl_of_isAmple_dual_toModules _ hJ hample j hj

end LargeDegree

section FieldExtension

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **Base change of a smooth curve.** The base change `X_K = X ×_{Spec k} Spec K` of a scheme
`X` smooth of relative dimension `n` over `k` along a field extension `K/k` is smooth of relative
dimension `n` over `K`.

(blueprint: `prose-C-04`, part (2)) -/
theorem smoothOfRelativeDimension_baseChange (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of k))] :
    SmoothOfRelativeDimension n (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback _ _) ‹_›

/-- **Base change of a proper scheme.** The base change `X_K` of a proper `k`-scheme `X` along a
field extension `K/k` is proper over `K`.

(blueprint: `prose-C-04`, part (2), and `lem-pc-projective-proper`) -/
theorem isProper_baseChange [IsProper (X ↘ Spec (.of k))] :
    IsProper (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
  IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›

/-- **Base change of a geometrically reduced scheme.** The base change `X_K` of a geometrically
reduced `k`-scheme `X`, e.g. a smooth one, along a field extension `K/k` is reduced.

(blueprint: `prose-C-04`, part (2)) -/
theorem isReduced_baseChange [GeometricallyReduced (X ↘ Spec (.of k))] :
    IsReduced (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  GeometricallyReduced.geometrically_isReduced (f := X ↘ Spec (.of k)) _ _ _
    (IsPullback.of_hasPullback _ _)

/-- **Smooth morphisms with geometrically connected fibres are geometrically integral**: their
base changes to fields are smooth over a field, hence regular, so they are reduced and, being
connected, irreducible.

(blueprint: `prose-C-04`, part (2)) -/
theorem _root_.AlgebraicGeometry.GeometricallyIntegral.of_smooth_of_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f :=
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have := Smooth.geometricallyReduced f
  .of_geometricallyReduced_of_geometricallyIrreducible f

/-- **Geometric integrality.** A smooth connected scheme `X` over a separably closed field `k`,
e.g. a smooth projective curve, is geometrically integral over `k`: it is geometrically
connected (`AlgebraicGeometry.GeometricallyConnected.of_isSepClosed`) and smooth.

(blueprint: `prose-C-04`, part (2)) -/
theorem _root_.AlgebraicGeometry.GeometricallyIntegral.of_isSepClosed [IsSepClosed k]
    [Smooth (X ↘ Spec (.of k))] [ConnectedSpace X] : GeometricallyIntegral (X ↘ Spec (.of k)) :=
  have := GeometricallyConnected.of_isSepClosed (k := k) X
  .of_smooth_of_geometricallyConnected _

/-- **Base change of a smooth curve is integral.** For a smooth connected scheme `X` over a
separably closed field `k`, e.g. a smooth projective curve, and a field extension `K/k`, the base
change `X_K = X ×_{Spec k} Spec K` is integral.

(blueprint: `prose-C-04`, part (2)) -/
theorem isIntegral_baseChange [IsSepClosed k] [Smooth (X ↘ Spec (.of k))] [ConnectedSpace X] :
    IsIntegral (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  (GeometricallyIntegral.of_isSepClosed (k := k) (X := X)).geometrically_isIntegral _ _ _
    (IsPullback.of_hasPullback _ _)

end FieldExtension

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **The degree of the dictionary.** Let `X` be a smooth projective curve of genus `g` over
`k` with `H⁰(X, 𝒪_X) = k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the
base change `X_K = X ×_{Spec k} Spec K` with `h^0(X_K, ℒ) = 1` and `H^q(X_K, ℒ) = 0` for
`q > 0`. Then `deg ℒ = χ(ℒ) - χ(𝒪_{X_K}) = 1 - (1 - g) = g`.

Of the hypothesis `H⁰(X, 𝒪_X) = k`, only `h⁰(X, 𝒪_X) = 1` is used, through
`χ(𝒪_{X_K}) = χ(𝒪_X) = h⁰(X, 𝒪_X) - g = 1 - g`. Without it the statement fails: for
`X = ℙ¹_ℂ` over `k = ℝ` and `K = ℂ`, the base change `X_ℂ` is two copies of `ℙ¹_ℂ`, so
`χ(𝒪_{X_ℂ}) = 2` rather than `1 - g = 1`, and the line bundle that is `𝒪(-1)` on one copy and
`𝒪` on the other has `χ(ℒ) = 1`, hence `deg ℒ = 1 - 2 = -1 ≠ g = 0`.

(blueprint: `proposition-divisors-degree-g-open-chart--1`) -/
theorem degree_eq_genus [GlobalSectionsBijective k X]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] (h0 : Modules.finrankH K ℒ 0 = 1)
    (hq : ∀ q : ℕ, 0 < q → Subsingleton (ℒ.H q)) :
    ℒ.degree K = (arithmeticGenus k X : ℤ) := by
  -- `X_K` is a smooth proper curve over `K` with `H⁰(X_K, 𝒪_{X_K}) = K`
  -- (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.pullback`), so Riemann–Roch applies.
  have : SmoothOfRelativeDimension 1 (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have hχ : ℒ.eulerChar K = 1 := by
    rw [Modules.eulerChar, finsum_eq_single _ 0 fun q hq0 ↦ ?_]
    · simp [h0]
    · have := hq q (Nat.pos_of_ne_zero hq0)
      simp [Modules.finrankH, Module.finrank_zero_of_subsingleton]
  rw [Modules.degree, hχ, eulerChar_unit_eq, arithmeticGenus_pullback]
  ring

/-- **The degree of a twist.** For an invertible sheaf `ℒ` on `X_K` and an invertible sheaf `ℳ`
on the smooth proper curve `X`, `deg (ℒ ⊗ ℳ_K) = deg ℒ + deg ℳ`, by additivity of the degree on
the smooth proper curve `X_K` and its invariance under base change.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem degree_tensorObj_pullback_fst
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible]
    (M : X.Modules) [M.IsInvertible] :
    (L ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K =
      L.degree K + M.degree k := by
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  rw [Modules.degree_tensorObj, Modules.degree_pullback]

local notation "𝔭" => Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- **The base change of a rational point has degree one.** For a `k`-rational point `x` of `X`,
the closed subscheme of `X_K` cut out by the pullback `(ker x) · 𝒪_{X_K}` of the ideal sheaf of
`x` is `Spec k ×_X X_K = Spec k ×_k Spec K = Spec K`, so it has `dim_K Γ = 1`. -/
theorem finrankΓ_subschemeι_comap_ker_fieldPoints (x : (X ↘ Spec (.of k)).fieldPoints k) :
    ((x.1.ker.comap 𝔭).subschemeι ≫ Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)).finrankΓ = 1 := by
  have hsq := (x.1.ker.isPullback_comap 𝔭).flip.paste_vert
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  -- the closed subscheme of `x` maps isomorphically to `Spec k`
  have hx : x.1 ≫ X ↘ Spec (.of k) = 𝟙 _ := by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have he : x.1.ker.subschemeι ≫ X ↘ Spec (.of k) = inv x.1.toImage := by
    rw [← cancel_epi x.1.toImage, ← Category.assoc, Hom.toImage_imageι, hx, IsIso.hom_inv_id]
  have : IsIso (x.1.ker.subschemeι ≫ X ↘ Spec (.of k)) := by
    rw [he]
    infer_instance
  have := hsq.isIso_snd_of_isIso
  rw [← Hom.finrankΓ_id (k := K)]
  exact Hom.finrankΓ_eq_of_iso _ _ (asIso ((x.1.ker.comap 𝔭).subschemeι ≫ pullback.snd _ _))
    (Iso.refl _) (by simp)

omit [IsProper (X ↘ Spec (.of k))] in
/-- **A section not vanishing at a point survives restriction to it.** Let `ℒ` be an invertible
sheaf on `X_K`, let `s : 𝒪_{X_K} ⟶ ℒ` be a global section and let `x` be a `k`-rational point
of `X` such that `s` does not vanish at `x_K`. Then some global section `z` of `ℒ` has non-zero
image in `H⁰(X_K, ℒ|_{x_K})`, where `ℒ|_{x_K}` is the cokernel of `𝓘 ⊗ ℒ ⟶ 𝒪_{X_K} ⊗ ℒ` for the
ideal sheaf `𝓘 = (ker x) · 𝒪_{X_K}` of `x_K`.

One can take `z` to be the class of `s`. Otherwise `s` factors through `𝓘 ⊗ ℒ ⟶ ℒ`, by left
exactness, so the zero scheme of `s` contains that of `𝓘 ⊗ ℒ ⟶ 𝒪 ⊗ ℒ`, which is `x_K`. -/
theorem exists_map_cokernel_π_ne_zero
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible]
    (s : 𝟙_ _ ⟶ L) (x : (X ↘ Spec (.of k)).fieldPoints k)
    (hx : ((X ↘ Spec (.of k)).baseChangeFieldPoint K x).1.base default ∉ s.zeroLocus.support) :
    ∃ z : L.H 0, Modules.H.map
      ((λ_ L).inv ≫ cokernel.π ((x.1.ker.comap 𝔭).toModulesι ▷ L)) 0 z ≠ 0 := by
  by_contra! h
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hJ := (Hom.isInvertible_ker_fieldPoints x).comap_of_flat 𝔭
  have := hJ.isInvertible_toModules
  set I := x.1.ker.comap 𝔭
  -- the class of `s` in `H⁰(ℒ|_{x_K})` vanishes, so `s` factors through `𝓘 ⊗ ℒ`
  have h0 : s ≫ (λ_ L).inv ≫ cokernel.π (I.toModulesι ▷ L) = 0 :=
    Modules.eq_zero_of_forall_H_map_zero _ fun z ↦ by
      rw [Modules.H.map_comp_apply]
      exact h _
  let S := ShortComplex.mk (I.toModulesι ▷ L) (cokernel.π _) (cokernel.condition _)
  have hS : S.Exact := ShortComplex.exact_cokernel _
  let t := hS.lift (s ≫ (λ_ L).inv) (by simpa using h0)
  have ht : t ≫ I.toModulesι ▷ L = s ≫ (λ_ L).inv := hS.lift_f _ _
  -- hence `Z(s) ⊇ Z(𝓘 ⊗ ℒ ⟶ 𝒪 ⊗ ℒ) = Z(𝓘 ⟶ 𝒪) = x_K`
  have := Modules.IsInvertible.sheafOfModules_isInvertible L
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (Limits.pullback
    (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (I.toModules ⊗ L)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (Limits.pullback
    (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules ⊗ L)
  have := Modules.IsInvertible.sheafOfModules_isInvertible I.toModules
  have hle : Modules.Hom.zeroLocus s ≤ I := by
    rw [Modules.Hom.zeroLocus_eq_of_arrowIso s (s ≫ (λ_ L).inv)
      (Arrow.isoMk (Iso.refl _) (λ_ L).symm), ← ht]
    refine (Modules.Hom.zeroLocus_comp_le _ _).trans ?_
    rw [Modules.Hom.zeroLocus_whiskerRight, hJ.zeroLocus_toModulesι]
  refine hx (IdealSheafData.support_antitone hle ?_)
  rw [← SetLike.mem_coe, IdealSheafData.coe_support_comap, Set.mem_preimage,
    Scheme.Hom.support_ker]
  rw [Hom.baseChangeFieldPoint, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  exact subset_closure ⟨_, rfl⟩

/-- **Removing a rational point.** Let `ℒ` be an invertible sheaf on `X_K`, let `s : 𝒪_{X_K} ⟶ ℒ`
be a global section and let `x` be a `k`-rational point of `X` such that `s` does not vanish at
`x_K`. Then twisting by the ideal sheaf `𝒪_X(-x) = ker x` lowers `h⁰` by exactly one:
`h⁰(X_K, ℒ ⊗ 𝒪_X(-x)_K) = h⁰(X_K, ℒ) - 1`.

The pullback of `𝒪_X(-x)` is the ideal sheaf `𝓘` of `x_K`, by flatness of `X_K ⟶ X`, and there
is an exact sequence `0 ⟶ 𝓘 ⊗ ℒ ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` for `i : x_K ⟶ X_K`. On global sections,
`H⁰(i_* i^* ℒ) = ℒ(x_K) ≅ K` is one-dimensional and `H⁰(ℒ) ⟶ ℒ(x_K)` is onto, since its image
contains `s(x_K) ≠ 0`; the claim follows from left exactness of `H⁰`.

(blueprint: `lemma-twisting-h-0-1-h`, Step 3) -/
theorem finrankH_zero_tensorObj_pullback_toModules_ker_add_one
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible]
    (s : 𝟙_ _ ⟶ L) (x : (X ↘ Spec (.of k)).fieldPoints k)
    (hx : ((X ↘ Spec (.of k)).baseChangeFieldPoint K x).1.base default ∉ s.zeroLocus.support) :
    Modules.finrankH K (L ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj x.1.ker.toModules) 0 + 1 =
      Modules.finrankH K L 0 := by
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hI := Hom.isInvertible_ker_fieldPoints x
  have hJ := hI.comap_of_flat 𝔭
  have := hJ.isInvertible_toModules
  obtain ⟨e₀⟩ := hI.nonempty_pullback_toModules_iso 𝔭 hJ
  -- the short exact sequence `0 ⟶ 𝓘 ⊗ ℒ ⟶ 𝒪 ⊗ ℒ ⟶ ℒ|_{x_K} ⟶ 0`
  let S := ShortComplex.mk ((x.1.ker.comap 𝔭).toModulesι ▷ L) (cokernel.π _)
    (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have e₁ : L ⊗ (Modules.pullback 𝔭).obj x.1.ker.toModules ≅ S.X₁ :=
    whiskerLeftIso L e₀ ≪≫ β_ _ _
  have e₂ : S.X₂ ≅ L := λ_ L
  have : S.X₂.IsInvertible := Modules.IsInvertible.of_iso e₂.symm
  have := hJ.finiteDimensional_H_cokernel_whiskerRight (k := K) L 0
  -- `h⁰(ℒ|_{x_K}) = 1`
  have h3 : Modules.finrankH K S.X₃ 0 = 1 := by
    have := hJ.subsingleton_H_one_cokernel_whiskerRight K L
    have h := hJ.eulerChar_cokernel_whiskerRight (k := K) L
    have h1 : Modules.finrankH K (cokernel ((x.1.ker.comap 𝔭).toModulesι ▷ L)) 1 = 0 :=
      Module.finrank_zero_of_subsingleton
    have := (x.1.ker.comap 𝔭).isQuasicoherent_cokernel_whiskerRight L
    rw [finrankΓ_subschemeι_comap_ker_fieldPoints,
      Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, h1] at h
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one, Nat.cast_eq_one] at h
    exact h
  -- the image of `H⁰(ℒ) ⟶ H⁰(ℒ|_{x_K})` is non-zero, hence everything
  let f := Modules.H.mapLinearMap K S.f 0
  let g := Modules.H.mapLinearMap K S.g 0
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Modules.H.injective_map_zero_of_shortExact hS)
  have hg : LinearMap.ker g = LinearMap.range f := by
    ext y
    exact SetLike.ext_iff.mp (Modules.H.ker_map_g_eq_range_map_f hS 0) y
  have hrg : Module.finrank K (LinearMap.range g) = 1 := by
    refine le_antisymm ((Submodule.finrank_le _).trans h3.le) ?_
    obtain ⟨z, hz⟩ := exists_map_cokernel_π_ne_zero K L s x hx
    refine Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hz ?_
    rw [Submodule.finrank_eq_zero] at h0
    have : g (Modules.H.map (λ_ L).inv 0 z) ∈ LinearMap.range g := ⟨_, rfl⟩
    rw [h0] at this
    rw [Modules.H.map_comp_apply]
    exact (Submodule.mem_bot K).mp this
  have hrf : Module.finrank K (LinearMap.range f) = Modules.finrankH K S.X₁ 0 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hf, finrank_bot] at this
    exact this.trans rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  rw [hg, hrg, hrf] at h2
  rw [Modules.finrankH_congr K e₁, ← Modules.finrankH_congr K e₂]
  change Modules.finrankH K S.X₁ 0 + 1 = Module.finrank K (S.X₂.H 0)
  omega

/-- **Descending induction on `h⁰`.** Let `ℒ` be an invertible sheaf on `X_K` and `ℳ` an
invertible sheaf on `X` with `h⁰(X_K, ℒ ⊗ ℳ_K) = t + 1` and `h¹(X_K, ℒ ⊗ ℳ_K) = 0`. Then there is
an invertible `ℒ₀ = ℳ(-x₁ - ⋯ - x_t)` on `X` with `h⁰(X_K, ℒ ⊗ ℒ₀_K) = 1` and
`h¹(X_K, ℒ ⊗ ℒ₀_K) = 0`.

At each step a non-zero section `s` of `ℒ ⊗ ℳ_K` does not vanish at some `x_K` with `x` a
`k`-rational point
(`AlgebraicGeometry.Scheme.Hom.exists_baseChangeFieldPoint_notMem_support_zeroLocus`).
Twisting by `𝒪_X(-x)` lowers `h⁰` by one
(`AlgebraicGeometry.Scheme.finrankH_zero_tensorObj_pullback_toModules_ker_add_one`) and lowers
`χ = h⁰ - h¹` by `deg 𝒪_X(-x) = -1`, so `h¹ = 0` is preserved.

(blueprint: `lemma-twisting-h-0-1-h`, Step 3) -/
theorem exists_isInvertible_twist_of_finrankH_zero_eq [IsSepClosed k]
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible] (t : ℕ) :
    ∀ M : X.Modules, M.IsInvertible →
      Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj M) 0 = t + 1 →
      Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj M) 1 = 0 →
      ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
        Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj ℒ₀) 0 = 1 ∧
        Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj ℒ₀) 1 = 0 := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  have := isReduced_baseChange (k := k) (X := X) K
  induction t with
  | zero => exact fun M hM h0 h1 ↦ ⟨M, hM, h0, h1⟩
  | succ t ih =>
  intro M hM h0 h1
  -- a non-zero global section `s` of `N = ℒ ⊗ M_K` and a rational point `x` at which it does
  -- not vanish
  have : Nontrivial ((L ⊗ (Modules.pullback 𝔭).obj M).H 0) :=
    Module.nontrivial_of_finrank_pos (R := K) (show 0 < Modules.finrankH K _ 0 by omega)
  obtain ⟨s, hs⟩ := Modules.exists_ne_zero_of_nontrivial_H_zero (L ⊗ (Modules.pullback 𝔭).obj M)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (L ⊗ (Modules.pullback 𝔭).obj M)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (Limits.pullback
    (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ s.zeroLocus.support := by
    by_contra! H
    refine hs ((Modules.Hom.zeroLocus_eq_bot_iff s).mp ?_)
    rw [← IdealSheafData.support_eq_top_iff]
    exact eq_top_iff.mpr fun y _ ↦ H y
  obtain ⟨x, hx⟩ :=
    (X ↘ Spec (.of k)).exists_baseChangeFieldPoint_notMem_support_zeroLocus K s ⟨y, hy⟩
  have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
  -- twist by the ideal sheaf `𝒪_X(-x)` of `x`
  obtain ⟨e⟩ := Modules.nonempty_pullback_tensorObj_iso 𝔭 M x.1.ker.toModules
  have h0' := finrankH_zero_tensorObj_pullback_toModules_ker_add_one K _ s x hx
  rw [← Modules.finrankH_congr K (whiskerLeftIso L e ≪≫ (α_ _ _ _).symm)] at h0'
  have hχ := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (L ⊗ (Modules.pullback 𝔭).obj (M ⊗ x.1.ker.toModules))
  have hχN := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (L ⊗ (Modules.pullback 𝔭).obj M)
  have hd := degree_tensorObj_pullback_fst K L (M ⊗ x.1.ker.toModules)
  have hdN := degree_tensorObj_pullback_fst K L M
  rw [Modules.degree_tensorObj (k := k) M, degree_toModules_ker_fieldPoints] at hd
  simp only [Modules.degree] at hd hdN
  refine ih (M ⊗ x.1.ker.toModules) inferInstance (by omega) ?_
  omega

/-- **The twist lemma.** Let `k` be separably closed, let `X` be a smooth projective connected
curve over `k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the base change
`X_K = X ×_{Spec k} Spec K`. Then there is a line bundle `ℒ₀` on `X` whose restriction to `X_K`
twists `ℒ` into the situation of `AlgebraicGeometry.Scheme.degree_eq_genus`:
`h^0(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h^1(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 0`.

The proof has three steps. Step 1: a `k`-rational point `x` gives the line bundle `𝒪_X(x)` of
degree one. Step 2: by Riemann–Roch on the smooth proper curve `X_K`, which has
`H⁰(X_K, 𝒪) = K`, the twist `ℒ ⊗ 𝒪_X(n x)_K` has `h⁰ ≥ 1` and `h¹ = 0` once its degree is at
least `2g`. Step 3: remove `h⁰ - 1` rational points
(`AlgebraicGeometry.Scheme.exists_isInvertible_twist_of_finrankH_zero_eq`).

(blueprint: `lemma-twisting-h-0-1-h`) -/
theorem exists_isInvertible_twist [IsSepClosed k] [ConnectedSpace X]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] :
    ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0 := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : GlobalSectionsBijective k X := .of_isSepClosed
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  -- Step 1: a line bundle `𝒪_X(x)` of degree one, from a rational point `x`
  obtain ⟨x⟩ := (X ↘ Spec (.of k)).nonempty_fieldPoints
  have hx := Hom.isInvertible_ker_fieldPoints x
  have := hx.isInvertible_dual_toModules
  have hdeg : ∀ n : ℕ, ∃ M : X.Modules, M.IsInvertible ∧ M.degree k = n := by
    intro n
    induction n with
    | zero => exact ⟨𝟙_ X.Modules, inferInstance, Modules.degree_unit k⟩
    | succ n ih =>
      obtain ⟨M, hM, hMd⟩ := ih
      refine ⟨x.1.ker.toModulesᵛ ⊗ M, inferInstance, ?_⟩
      rw [Modules.degree_tensorObj, hMd, hx.degree_dual_toModules_eq_one
        ((X ↘ Spec (.of k)).finrankΓ_subschemeι_ker_fieldPoints x)]
      push_cast
      ring
  -- Step 2: twist by `𝒪_X(n x)` for `n ≫ 0` to reach `h⁰ ≥ 1` and `h¹ = 0`, by Riemann–Roch
  set g := arithmeticGenus K (Limits.pullback (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  obtain ⟨M, hM, hMd⟩ := hdeg (2 * g - ℒ.degree K).toNat
  have hd := degree_tensorObj_pullback_fst K ℒ M
  have hd' : 2 * (g : ℤ) - 1 ≤ (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K := by
    rw [hd, hMd]
    omega
  have h0 := finrankH_zero_eq _ hd'
  have hχ := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M)
  have hχ₀ := eulerChar_unit_eq (k := K) (X := Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  simp only [Modules.degree] at hd hd' h0 hMd
  -- Step 3: remove `h⁰ - 1` rational points
  refine exists_isInvertible_twist_of_finrankH_zero_eq K ℒ
    (Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) 0 - 1) M hM (by omega) (by omega)

end BaseChange

end AlgebraicGeometry.Scheme
