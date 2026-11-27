import Langlands.BaseChange.TwistedLocalDescent.BlockDeterminant
import Langlands.BaseChange.LeviClassSystem
import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.RegularLeviNormRepresentative
import Langlands.BaseChange.SigmaInducedIntertwiner

/-! # Levi parts of parabolic elements in a σ-regular twisted class

Let `E/F` be a cyclic algebra of group `⟨σ⟩`, `δ ∈ GL_n(E)` norm-associated with a regular
semisimple `γ`, `m` a Levi class system of `γ`, and `d j ∈ M(E)` whose blockwise norms are the
blocks of `m j`. If `p ∈ P(E)` is twisted conjugate to `δ` in `G(E)`, then the Levi part of `p`
is `M(E)`-twisted conjugate to one of the `d j`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Langlands.JacquetLanglands
open _root_.Polynomial

universe u v

section Charpoly

variable {R : Type v} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- The characteristic polynomial of a block upper triangular element is the product of those
of its diagonal blocks. -/
theorem charpoly_parabolic (p : B.parabolic R) :
    (p : GeneralLinear n R).val.charpoly =
      ∏ i, (B.leviProjection R p i).val.charpoly := by
  classical
  have ht : (p : GeneralLinear n R).val.BlockTriangular B.coordinateBlock := by
    intro a c hca
    obtain ⟨⟨i, s⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, t⟩, rfl⟩ := B.indexEquiv.surjective c
    have hji : j < i := by
      simpa only [BlockShape.coordinateBlock, Equiv.symm_apply_apply] using hca
    exact (B.mem_parabolic_iff R p).mp p.property i j s t hji
  rw [ht.charpoly]
  have hs : Function.Surjective B.coordinateBlock :=
    fun i => ⟨B.index i ⟨0, B.positive i⟩, coordinateBlock_index B i _⟩
  rw [Finset.image_univ_of_surjective hs]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e : Fin (B.size i) ≃ {x : Fin n // B.coordinateBlock x = i} :=
    Equiv.ofBijective (fun a => ⟨B.index i a, coordinateBlock_index B i a⟩)
      ⟨fun a b h => (B.index i).injective (congrArg Subtype.val h), fun y => by
        obtain ⟨y, hy⟩ := y
        obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
        have : j = i := by
          simpa only [BlockShape.coordinateBlock, Equiv.symm_apply_apply] using hy
        subst this
        exact ⟨b, rfl⟩⟩
  rw [← Matrix.charpoly_reindex e.symm]
  congr 1

end Charpoly

section Norm

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B : BlockShape n)

/-- The cyclic norm of a parabolic element, as a parabolic element. -/
def parabolicCyclicNorm (l : ℕ) (p : B.parabolic E) : B.parabolic E :=
  ⟨cyclicNorm σ l (p : GeneralLinear n E), by
    induction l with
    | zero => exact (B.parabolic E).one_mem
    | succ l ih =>
      rw [cyclicNorm_succ]
      exact (B.parabolic E).mul_mem ih ((entrywiseAut_mem_parabolic_iff (σ ^ l) B p).2 p.2)⟩

theorem leviProjection_parabolicCyclicNorm (l : ℕ) (p : B.parabolic E) (i : Fin B.length) :
    B.leviProjection E (parabolicCyclicNorm σ B l p) i =
      cyclicNorm σ l (B.leviProjection E p i) := by
  induction l with
  | zero =>
    have : parabolicCyclicNorm σ B 0 p = 1 := Subtype.ext (cyclicNorm_zero σ (p : GeneralLinear n E))
    rw [this, map_one, cyclicNorm_zero]
    rfl
  | succ l ih =>
    have hsplit : parabolicCyclicNorm σ B (l + 1) p =
        parabolicCyclicNorm σ B l p * parabolicAut (σ ^ l) B p :=
      Subtype.ext (cyclicNorm_succ σ l _)
    rw [hsplit, map_mul, Pi.mul_apply, ih, leviProjection_parabolicAut, cyclicNorm_succ]
    rfl

end Norm

section Classification

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ}
  {n : ℕ} (B : BlockShape n)

theorem charpoly_baseChange {r : ℕ} (γ : GeneralLinear r F) :
    (baseChange F E r γ).val.charpoly = (γ.val.charpoly).map (algebraMap F E) := by
  rw [← Matrix.charpoly_map]
  rfl

/-- **Classification of Levi parts.** Let `E/F` be a cyclic algebra of group `⟨σ⟩`. If
`p ∈ P(E)` is a twisted conjugate of `δ`, which is norm-associated with a regular semisimple `γ`,
then the Levi part of `p` is twisted conjugate in `M(E)` to one of the Levi representatives `d j`
(elements whose blockwise norms are the blocks of a Levi class system `m` of `γ`). -/
theorem exists_levi_twistedConj_of_parabolic (hE : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hδ : IsNormAssociated σ l δ γ)
    (hγ : IsRegularSemisimple γ) {k : ℕ} {m : Fin k → B.Levi F} (hm : IsLeviClassSystem B γ m)
    {d : Fin k → B.Levi E}
    (hd : ∀ j i, cyclicNorm σ l (d j i) = baseChange F E (B.size i) (m j i))
    (g : GeneralLinear n E) (p : B.parabolic E)
    (hp : (p : GeneralLinear n E) = g⁻¹ * δ * entrywiseAut σ n g) :
    ∃ j, ∃ y : B.Levi E, y⁻¹ * B.leviProjection E p * leviAut σ B y = d j := by
  classical
  have hσ := hE.pow_eq_one
  have hNL := fun r => cyclicNormLemma.{u, v} F E σ l r hE
  have hassoc := fun r => (hNL r).1
  have hconj := fun r => (hNL r).2.2
  set x := B.leviProjection E p
  -- Rational associates of the blocks of the Levi part.
  choose γ' hγ' using fun i => hassoc (B.size i) (x i)
  -- Characteristic polynomials.
  have hNp : (parabolicCyclicNorm σ B l p : GeneralLinear n E).val.charpoly =
      ((B.leviEmbedding F γ').val.charpoly).map (algebraMap F E) := by
    rw [charpoly_parabolic, charpoly_leviEmbedding, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [leviProjection_parabolicCyclicNorm]
    obtain ⟨h, hh⟩ := hγ' i
    rw [← charpoly_baseChange, ← hh, charpoly_conj]
  have hNp' : (parabolicCyclicNorm σ B l p : GeneralLinear n E).val.charpoly =
      (γ.val.charpoly).map (algebraMap F E) := by
    change (cyclicNorm σ l (p : GeneralLinear n E)).val.charpoly = _
    rw [hp, cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, charpoly_conj]
    obtain ⟨h, hh⟩ := hδ
    rw [← charpoly_baseChange, ← hh, charpoly_conj]
  have hcp : (B.leviEmbedding F γ').val.charpoly = γ.val.charpoly :=
    Polynomial.map_injective _ (algebraMap F E).injective (hNp.symm.trans hNp')
  -- `γ` and the block diagonal element are conjugate.
  have hγconj : ∃ z : GeneralLinear n F, z⁻¹ * γ * z = B.leviEmbedding F γ' := by
    obtain ⟨z, hz⟩ := exists_matrix_conj_of_charpoly_eq_of_separable γ.val
      (B.leviEmbedding F γ').val hγ hcp
    refine ⟨z⁻¹, Units.ext ?_⟩
    rw [inv_inv]
    exact hz
  obtain ⟨j, y, hy⟩ := hm.2.2 γ' hγconj
  refine ⟨j, ?_⟩
  -- Blockwise twisted conjugacy.
  have hblock : ∀ i, ∃ w : GeneralLinear (B.size i) E,
      w⁻¹ * x i * entrywiseAut σ (B.size i) w = d j i := by
    intro i
    apply hconj (B.size i) (x i) (d j i)
    obtain ⟨h, hh⟩ := hγ' i
    have hyi : (y i)⁻¹ * m j i * y i = γ' i := congrFun hy i
    let b := baseChange F E (B.size i) (y i)
    refine ⟨h * b⁻¹, ?_⟩
    calc (h * b⁻¹)⁻¹ * cyclicNorm σ l (x i) * (h * b⁻¹) =
          b * (h⁻¹ * cyclicNorm σ l (x i) * h) * b⁻¹ := by group
      _ = b * baseChange F E (B.size i) (γ' i) * b⁻¹ := by rw [hh]
      _ = baseChange F E (B.size i) (y i * γ' i * (y i)⁻¹) := by
        simp only [b, map_mul, map_inv]
      _ = cyclicNorm σ l (d j i) := by
        rw [hd j i, ← hyi]
        congr 1
        group
  choose w hw using hblock
  refine ⟨w, funext fun i => ?_⟩
  simp only [Pi.mul_apply, Pi.inv_apply, leviAut_apply]
  exact hw i

end Classification

end Langlands.BaseChange.TwistedLocalDescent
