/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Mathlib.RingTheory.Extension.Cotangent.Basis
import WeilConjectures.RingTheory.SmoothQuotientFibreDifferentialRank
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.RingTheory.ImprovePresentationSmoothConormalFree

/-!
# Smooth retract by a relative global complete intersection

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CG (lemma-syntomic-complete-intersection),
line 567 and proof lines 580--588 (blueprint:
lem-weil-pbc-smooth-retract-relative-global-complete-intersection).
-/

@[expose] public section

universe u v

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- Identify the extension cotangent module with its quotient-ring incarnation. -/
private noncomputable def quotientCotangentEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension R S) :
    let ψ := Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId P.Ring S) P.algebraMap_surjective
    letI : Algebra (P.Ring ⧸ P.ker) S := ψ.toRingHom.toAlgebra
    P.Cotangent ≃ₗ[P.Ring ⧸ P.ker] P.ker.Cotangent := by
  let ψ := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId P.Ring S) P.algebraMap_surjective
  let : Algebra (P.Ring ⧸ P.ker) S := ψ.toRingHom.toAlgebra
  exact
    { toFun := Extension.Cotangent.val
      invFun := Extension.Cotangent.of
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' q x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        change (algebraMap P.Ring S r • x).val =
          Ideal.Quotient.mk P.ker r • x.val
        rw [algebraMap_smul S, Extension.Cotangent.val_smul',
          ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial renaming identifies the conormal modules. -/
private noncomputable def reindexCotangentEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι ι' : Type*} (P : Generators R S ι) (e : ι' ≃ ι) :
    P.toExtension.Cotangent ≃ₗ[S] (P.reindex e).toExtension.Cotangent := by
  let f : P.Hom (P.reindex e) :=
    { val i := MvPolynomial.X (e.symm i)
      aeval_val i := by simp [Generators.reindex] }
  let g : (P.reindex e).Hom P :=
    { val i := MvPolynomial.X (e i)
      aeval_val i := by simp [Generators.reindex] }
  let fm := Extension.Cotangent.map f.toExtensionHom
  let gm := Extension.Cotangent.map g.toExtensionHom
  have hgf : g.comp f = Generators.Hom.id P := by
    ext i
    simp [g, f, Generators.Hom.comp]
  have hfg : f.comp g = Generators.Hom.id (P.reindex e) := by
    ext i
    simp [g, f, Generators.Hom.comp]
  exact
    { fm with
      invFun := gm
      left_inv x := by
        have h := congrArg (fun t ↦ Extension.Cotangent.map t.toExtensionHom) hgf
        simpa [Generators.Hom.toExtensionHom_comp, Extension.Cotangent.map_comp, fm, gm]
          using DFunLike.congr_fun h x
      right_inv x := by
        have h := congrArg (fun t ↦ Extension.Cotangent.map t.toExtensionHom) hfg
        simpa [Generators.Hom.toExtensionHom_comp, Extension.Cotangent.map_comp, fm, gm]
          using DFunLike.congr_fun h x }

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Algebra, Lemma 07CF.
(blueprint: lem-weil-pbc-conormal-free-presentation-basis)

Proof. Form the generators attached to the surjective polynomial map. Identify their
cotangent module with the kernel cotangent module, transporting freeness through the
quotient equivalence to S. Apply Mathlib's Huber lemma to obtain a presentation whose
relations form a conormal basis. Reindex its finite variable and relation types by Fin.
The polynomial renaming equivalence transports the conormal basis. Finally identify S
with the quotient by its presentation kernel, replace that kernel by the span of the
relations, and transport the coefficients and basis through the quotient equivalence.
-/
private theorem finite_conormal_basis_presentation
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [FinitePresentation R S] (m : ℕ) (g : MvPolynomial (Fin m) R →ₐ[R] S)
    (hg : Function.Surjective g) (J : Ideal (MvPolynomial (Fin m) R))
    (hJ : J = RingHom.ker g.toRingHom)
    (hfree : Module.Free (MvPolynomial (Fin m) R ⧸ J) J.Cotangent) :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
      (_ψ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] S)
      (b : Module.Basis (Fin c)
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        (Ideal.span (Set.range f)).Cotangent),
      ∀ j : Fin c, b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ := by
  classical
  subst J
  let G := Generators.ofAlgHom g hg
  have : Module.Free (G.Ring ⧸ G.ker) G.ker.Cotangent := by
    change Module.Free (MvPolynomial (Fin m) R ⧸ G.ker) G.ker.Cotangent
    rw [Generators.ker_ofAlgHom]
    exact hfree
  let φ := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId G.toExtension.Ring S) G.toExtension.algebraMap_surjective
  let : Algebra (G.Ring ⧸ G.ker) S := φ.toRingHom.toAlgebra
  let b₀ := (Module.Free.chooseBasis (G.Ring ⧸ G.ker) G.ker.Cotangent).map
    (quotientCotangentEquiv G.toExtension).symm
  let bG := b₀.mapCoeffs φ.toRingEquiv (fun _ _ ↦ rfl)
  have : Module.Free S G.toExtension.Cotangent := Module.Free.of_basis bG
  obtain ⟨P, b, _, hb⟩ := G.exists_presentation_of_free_cotangent
  let e := (Fintype.equivFin (Unit ⊕ Fin m)).symm
  let d := (Fintype.equivFin (Unit ⊕ Fin (Module.finrank S G.toExtension.Cotangent))).symm
  let P' := P.reindex e d
  let b' := (b.map (reindexCotangentEquiv P.toGenerators e)).reindex d.symm
  have hb' : ∀ j, b' j = Extension.Cotangent.mk
      ⟨P'.relation j, P'.relation_mem_ker j⟩ := by
    intro j
    simp only [b', Module.Basis.reindex_apply, Module.Basis.map_apply, hb]
    simp [reindexCotangentEquiv, P', Presentation.reindex,
      MvPolynomial.rename_eq_aeval, Generators.Hom.toAlgHom]
    rfl
  let ψ := P'.quotientEquiv.restrictScalars R
  let : Algebra P'.Quotient S := P'.quotientEquiv.toRingHom.toAlgebra
  let bQ := (b'.mapCoeffs P'.quotientEquiv.symm.toRingEquiv
    (fun s x ↦ by
      change (P'.quotientEquiv (P'.quotientEquiv.symm s)) • x = s • x
      rw [P'.quotientEquiv.apply_symm_apply])).map (quotientCotangentEquiv P'.toExtension)
  have hbQ : ∀ j, bQ j = P'.ker.toCotangent
      ⟨P'.relation j, P'.relation_mem_ker j⟩ := by
    intro j
    simp only [bQ, Module.Basis.map_apply, Module.Basis.mapCoeffs_apply]
    dsimp only [quotientCotangentEquiv, LinearEquiv.coe_mk]
    exact congrArg Extension.Cotangent.val (hb' j)
  have result : ∃ (_ψ : (P'.Ring ⧸ P'.ker) ≃ₐ[R] S)
      (b : Module.Basis _ (P'.Ring ⧸ P'.ker) P'.ker.Cotangent),
      ∀ j (hj : P'.relation j ∈ P'.ker),
        b j = P'.ker.toCotangent ⟨P'.relation j, hj⟩ :=
    ⟨ψ, bQ, fun j _ ↦ hbQ j⟩
  rw [← P'.span_range_relation_eq_ker] at result
  obtain ⟨ψQ, bQ, hQ⟩ := result
  exact ⟨_, _, P'.relation, ψQ, bQ, fun j ↦ hQ j _⟩

/-- Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CG, and the
split conormal sequence in the proof of Lemma 07CH.
(blueprint: lem-weil-pbc-smooth-retract-relative-global-complete-intersection)

Proof. The conormal sequence of the polynomial quotient splits because the quotient
is smooth. Its middle term has rank n, and the given equation basis makes its left
term free of rank c. Tensoring this split sequence with any residue field shows that
c is at most n and that the differential fibre has rank n-c. For a nonempty fibre
over a prime of R, smoothness and differentials commute with base change. Thus at
every prime of this fibre the differential fibre has rank n-c. The dimension theorem
for a smooth finite type algebra over a field identifies this rank with dimension at
the point. Dimension is the supremum of dimensions at points; because this fibre is
nontrivial its spectrum is nonempty, and the constant supremum is n-c. Empty fibres
impose no condition, so the same argument includes the zero ring.
-/
private theorem smooth_conormal_basis_fibre_dimension
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent) :
    IsRelativeGlobalCompleteIntersectionPresentation f := by
  classical
  intro p hp hnontrivial
  let Q := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let T := p.Fiber Q
  have : Nontrivial T := hnontrivial
  have : Smooth p.ResidueField T := inferInstance
  have hpoint (q : PrimeSpectrum T) :
      c ≤ n ∧ topologicalKrullDimAt q = (n - c : ℕ) := by
    obtain ⟨hcn, hrank⟩ := smooth_quotient_fibre_differential_rank f b p q
    have : Smooth T (Localization.Away (1 : T)) :=
      Smooth.of_isLocalization_Away (1 : T)
    have hsm : IsSmoothAtPrime p.ResidueField q :=
      ⟨1, q.asIdeal.one_notMem,
        Smooth.comp p.ResidueField T (Localization.Away (1 : T))⟩
    obtain ⟨_, hdim⟩ :=
      finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime q hsm
    refine ⟨hcn, ?_⟩
    rw [← hdim, hrank]
  obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum T))
  refine ⟨(hpoint q).1, ?_⟩
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  simp only [(hpoint _).2, ciSup_const]

/-- A smooth algebra is a retract of a relative global complete intersection that is smooth over it.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07CG
(blueprint: lem-weil-pbc-smooth-retract-relative-global-complete-intersection).

Proof:
1. Apply lem-weil-pbc-improve-presentation-smooth-conormal-free to obtain a smooth
   `A`-algebra `C₀` with an `A`-algebra retraction and a polynomial presentation with free
   conormal module. Composition of smooth maps makes `C₀` smooth, hence finitely presented,
   over `R` (lem-weil-pbc-smooth-ring-map-base-change-composition).
2. Apply lem-weil-pbc-conormal-free-presentation-basis (07CF) to get `n,c,f` and an
   `R`-algebra isomorphism `ψ : R[x]/(f) ≃ C₀` with equation classes a conormal basis.
   Transport smoothness over `R` across `ψ`.
3. Set `σ = ψ⁻¹ ∘ (A → C₀)` and `π = ρ ∘ ψ`. Cancellation gives `π ∘ σ = id`.
   Give the quotient its `A`-algebra structure through `σ`; then `ψ` is an `A`-algebra
   isomorphism, so it transports smoothness over `A` as well.
4. Apply lem-weil-pbc-smooth-quotient-fibre-differential-rank to the quotient and its
   conormal basis: for each prime of a fibre, `c ≤ n` and the differential fibre has
   rank `n - c`. This remaining rank calculation is stated in its own module.
5. For a prime of `R`, the fibre is smooth over its residue field by base change.
   Lemma lem-weil-pbc-smooth-over-field-dimension-differentials identifies the dimension
   at every point of this fibre with that rank.
6. For a nonempty fibre, lem-weil-pbc-dimension-supremum-local-dimensions identifies
   its dimension with the supremum of these constant point dimensions, hence `n - c`.
   This is the specified relative global complete-intersection condition.
-/
theorem smooth_retract_relative_global_complete_intersection
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [Smooth R A] :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      IsRelativeGlobalCompleteIntersectionPresentation f ∧
      (∃ b : Module.Basis (Fin c)
          (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
          (Ideal.span (Set.range f)).Cotangent,
        ∀ j : Fin c,
          b j = (Ideal.span (Set.range f)).toCotangent
            ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) ∧
      (∃ (σ : A →ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
          (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] A),
        π.comp σ = AlgHom.id R A ∧
        ∃ (_ : Algebra A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))),
          (Algebra.ofId A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))).toRingHom =
              σ.toRingHom ∧
          Smooth A (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  classical
  obtain ⟨C, _, _, _, _, _, ρ, hρ, m, g, hg, J, hJ, hfree⟩ :=
    improve_presentation_smooth_conormal_free R A
  have : Smooth R C := Smooth.comp R A C
  obtain ⟨n, c, f, ψ, b, hb⟩ :=
    finite_conormal_basis_presentation R C m g hg J hJ hfree
  let Q := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  have : Smooth R Q := Smooth.of_equiv ψ.symm
  have hci : IsRelativeGlobalCompleteIntersectionPresentation f :=
    smooth_conormal_basis_fibre_dimension f b
  let σ : A →ₐ[R] Q := ψ.symm.toAlgHom.comp (IsScalarTower.toAlgHom R A C)
  let π : Q →ₐ[R] A := (ρ.restrictScalars R).comp ψ.toAlgHom
  refine ⟨n, c, f, hci, ⟨b, hb⟩, σ, π, ?_, ?_⟩
  · ext a
    change ρ (ψ (ψ.symm (algebraMap A C a))) = a
    rw [ψ.apply_symm_apply]
    exact DFunLike.congr_fun hρ a
  · let : Algebra A Q := σ.toRingHom.toAlgebra
    refine ⟨inferInstance, rfl, ?_⟩
    let e : Q ≃ₐ[A] C :=
      { ψ.toRingEquiv with
        commutes' a := by
          change ψ (ψ.symm (algebraMap A C a)) = algebraMap A C a
          exact ψ.apply_symm_apply _ }
    exact Smooth.of_equiv e.symm

end Algebra
