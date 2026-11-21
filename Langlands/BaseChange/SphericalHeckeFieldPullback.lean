import Langlands.BaseChange.UnramifiedBaseChangeHom
import Langlands.LocalFactor.Ramification.UniformizerCriterionProof
import Langlands.Representation.RankinSelberg.FieldTransport.Padic

/-! Transport of spherical Hecke functions along a p-adic field isomorphism. -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified MeasureTheory
open Langlands.RankinSelberg.FieldTransport

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- The entrywise topological group isomorphism under the canonical topologies. -/
def padicMatrixFieldEquiv (n : ℕ) :
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n E.Carrier :=
  Langlands.GeneralLinear.fieldEquiv n e.toRingEquiv
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E e)
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F e.symm)

@[simp] theorem padicMatrixFieldEquiv_apply_apply (n : ℕ)
    (g : GeneralLinear n F.Carrier) (i j : Fin n) :
    padicMatrixFieldEquiv F E e n g i j = e (g i j) := rfl

theorem padicMatrixFieldEquiv_mem_spherical_iff (r : ℕ)
    (g : GeneralLinear (r + 1) F.Carrier) :
    padicMatrixFieldEquiv F E e (r + 1) g ∈ sphericalOpenSubgroup E r ↔
      g ∈ sphericalOpenSubgroup F r := by
  change padicMatrixFieldEquiv F E e (r + 1) g ∈
    Conductor.integralSubgroup E.canonicalTopologicalData.Integers r ↔
      g ∈ Conductor.integralSubgroup F.canonicalTopologicalData.Integers r
  rw [← Conductor.levelSubgroup_zero, ← Conductor.levelSubgroup_zero]
  exact fieldEquiv_mem_levelOpenSubgroup_zero_iff e.toRingEquiv
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E e)
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F e.symm)
    (algEquiv_mem_integers_iff F E e) r g

theorem padicMatrixFieldEquiv_measurePreserving (r : ℕ) :
    MeasurePreserving (padicMatrixFieldEquiv F E e (r + 1))
      (sphericalHaar F r) (sphericalHaar E r) :=
  ⟨(padicMatrixFieldEquiv F E e (r + 1)).continuous.measurable,
    normalizedCompactOpenHaar_map _ _ _ _ _ (padicMatrixFieldEquiv_mem_spherical_iff F E e r)⟩

variable (r : ℕ)

local notation "κ" => padicMatrixFieldEquiv F E e (r + 1)

private def pullbackFn (φ : SphericalHeckeAlgebra E r) : SphericalHeckeAlgebra F r :=
  ⟨Hecke.TestFunction.pullback (κ).toHomeomorph
      (Hecke.HeckeAlgebra.toTestFunction _ φ.val), by
    constructor
    · intro k x
      change φ (κ (k.val * x)) = φ (κ x)
      rw [map_mul]
      exact Hecke.HeckeAlgebra.Corner.leftInvariant _ _ _ φ
        ⟨κ k, (padicMatrixFieldEquiv_mem_spherical_iff F E e r k).2 k.property⟩ (κ x)
    · intro k x
      change φ (κ (x * k.val)) = φ (κ x)
      rw [map_mul]
      exact Hecke.HeckeAlgebra.Corner.rightInvariant _ _ _ φ
        ⟨κ k, (padicMatrixFieldEquiv_mem_spherical_iff F E e r k).2 k.property⟩ (κ x)⟩

private theorem pullbackFn_apply (φ : SphericalHeckeAlgebra E r)
    (g : GeneralLinear (r + 1) F.Carrier) :
    pullbackFn F E e r φ g = φ (κ g) := rfl

private theorem spherical_ext {φ ψ : SphericalHeckeAlgebra F r}
    (h : ∀ g, φ g = ψ g) : φ = ψ :=
  Subtype.ext (Hecke.HeckeAlgebra.ext _ h)

private theorem pullbackFn_one :
    pullbackFn F E e r 1 = 1 := by
  apply spherical_ext
  intro g
  change (1 : SphericalHeckeAlgebra E r) (κ g) = (1 : SphericalHeckeAlgebra F r) g
  rw [← standardHeckeElement_zero E r, ← standardHeckeElement_zero F r,
    standardHeckeElement_apply, standardHeckeElement_apply,
    standardDiagonal_zero, standardDiagonal_zero, Hecke.TestFunction.doubleCosetSet_one,
    Hecke.TestFunction.doubleCosetSet_one]
  by_cases hg : g ∈ sphericalOpenSubgroup F r
  · rw [Set.indicator_of_mem ((padicMatrixFieldEquiv_mem_spherical_iff F E e r g).2 hg),
      Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem (fun hk =>
      hg ((padicMatrixFieldEquiv_mem_spherical_iff F E e r g).1 hk)), Set.indicator_of_notMem hg]

/-- Precomposition with the matrix isomorphism respects spherical convolution and the unit. -/
def sphericalHeckeFieldPullback : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r where
  toFun := pullbackFn F E e r
  map_one' := pullbackFn_one F E e r
  map_mul' φ ψ := by
    apply spherical_ext
    intro g
    change (φ * ψ) (κ g) = (pullbackFn F E e r φ * pullbackFn F E e r ψ) g
    rw [Hecke.HeckeAlgebra.Corner.mul_apply, Hecke.HeckeAlgebra.Corner.mul_apply]
    have h := (padicMatrixFieldEquiv_measurePreserving F E e r).integral_comp
      (κ).toHomeomorph.measurableEmbedding (fun y => φ y * ψ (y⁻¹ * κ g))
    simpa only [pullbackFn_apply, Function.comp_apply, ← map_inv, ← map_mul] using h.symm
  map_zero' := by
    apply spherical_ext
    intro g
    rfl
  map_add' φ ψ := by
    apply spherical_ext
    intro g
    rfl
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change c • pullbackFn F E e r 1 = c • 1
    rw [pullbackFn_one]

@[simp] theorem sphericalHeckeFieldPullback_apply (φ : SphericalHeckeAlgebra E r)
    (g : GeneralLinear (r + 1) F.Carrier) :
    sphericalHeckeFieldPullback F E e r φ g = φ (κ g) := rfl

private theorem standardDiagonal_image_mem (i : Fin (r + 2)) :
    κ (standardDiagonal F r i) ∈
      Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup E r) (standardDiagonal E r i) := by
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let u : E.Carrierˣ := Units.map e.toMonoidHom T.uniformizerUnit * S.uniformizerUnit⁻¹
  let d : Fin (r + 1) → E.Carrierˣ := fun j => if j.val < i.val then u else 1
  let k := Langlands.GeneralLinear.Iwasawa.diagonalUnits d
  have hu : S.ord (u : E.Carrier) = 0 := by
    have hT : T.uniformizer ≠ 0 := T.uniformizerUnit.ne_zero
    have hS : S.uniformizer ≠ 0 := S.uniformizerUnit.ne_zero
    change S.ord (e T.uniformizer * S.uniformizer⁻¹) = 0
    rw [S.ord_mul ((map_ne_zero e).2 hT) (inv_ne_zero hS),
      S.ord_inv, PadicField.CanonicalTransport.ord_map F E e, T.ord_uniformizer, S.ord_uniformizer]
    norm_num
  have hd (j : Fin (r + 1)) : S.ord (d j : E.Carrier) = 0 := by
    by_cases hj : j.val < i.val
    · simpa only [d, ite_eq_left hj] using hu
    · simp only [d, ite_eq_right hj, Units.val_one, S.ord_one]
  have hdi (j : Fin (r + 1)) : (d j : E.Carrier) ∈ S.Integers :=
    (S.mem_integers_iff_zero_le_ord (d j).ne_zero).2 ((hd j).ge)
  have hdii (j : Fin (r + 1)) : ((d j)⁻¹ : E.Carrierˣ).val ∈ S.Integers := by
    apply (S.mem_integers_iff_zero_le_ord ((d j)⁻¹).ne_zero).2
    rw [Units.val_inv_eq_inv_val, S.ord_inv, hd, neg_zero]
  have hk : k ∈ sphericalOpenSubgroup E r := by
    change k ∈ Conductor.integralSubgroup S.Integers r
    rw [Conductor.mem_integralSubgroup]
    constructor
    · intro a b
      change (Matrix.diagonal (fun j => (d j : E.Carrier))) a b ∈ S.Integers
      by_cases h : a = b
      · simpa [h] using hdi b
      · simp [Matrix.diagonal_apply_ne _ h]
    · intro a b
      change ((Langlands.GeneralLinear.Iwasawa.diagonalUnits d)⁻¹) a b ∈ S.Integers
      rw [← map_inv]
      change (Matrix.diagonal (fun j => ((d j)⁻¹ : E.Carrierˣ).val)) a b ∈ S.Integers
      by_cases h : a = b
      · simpa [h] using hdii b
      · simp [Matrix.diagonal_apply_ne _ h]
  have heq : κ (standardDiagonal F r i) = k * standardDiagonal E r i := by
    rw [show standardDiagonal E r i = Langlands.GeneralLinear.Iwasawa.diagonalUnits
      (fun j => if j.val < i.val then S.uniformizerUnit else 1) from rfl, ← map_mul]
    apply Units.ext
    ext a b
    change κ (standardDiagonal F r i) a b = Matrix.diagonal _ a b
    rw [padicMatrixFieldEquiv_apply_apply, standardDiagonal_val]
    by_cases hab : a = b
    · subst b
      by_cases ha : a.val < i.val
      · simp [d, ha, u, T, S, mul_assoc]
      · simp [d, ha]
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, map_zero]
  exact (Hecke.TestFunction.mem_doubleCosetSet _ _ _).2
    ⟨k, hk, 1, (sphericalOpenSubgroup E r).one_mem, by simpa only [mul_one] using heq⟩

theorem sphericalHeckeFieldPullback_standard (i : Fin (r + 2)) :
    sphericalHeckeFieldPullback F E e r (standardHeckeElement E r i) =
      standardHeckeElement F r i := by
  apply spherical_ext
  intro g
  rw [sphericalHeckeFieldPullback_apply, standardHeckeElement_apply, standardHeckeElement_apply,
    ← Hecke.TestFunction.doubleCosetSet_eq_of_mem _ (standardDiagonal_image_mem F E e r i)]
  have hmem :
      κ g ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup E r)
          (κ (standardDiagonal F r i)) ↔
        g ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) (standardDiagonal F r i) := by
    simp only [Hecke.TestFunction.mem_doubleCosetSet]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      obtain ⟨a, rfl⟩ := (κ).surjective a
      obtain ⟨b, rfl⟩ := (κ).surjective b
      exact ⟨a, (padicMatrixFieldEquiv_mem_spherical_iff F E e r a).1 ha,
        b, (padicMatrixFieldEquiv_mem_spherical_iff F E e r b).1 hb,
        (κ).injective (by simpa only [map_mul] using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨κ a, (padicMatrixFieldEquiv_mem_spherical_iff F E e r a).2 ha,
        κ b, (padicMatrixFieldEquiv_mem_spherical_iff F E e r b).2 hb, by simp only [map_mul]⟩
  by_cases hg : g ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) (standardDiagonal F r i)
  · rw [Set.indicator_of_mem (hmem.2 hg), Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem (fun h => hg (hmem.1 h)), Set.indicator_of_notMem hg]

/-- The Satake condition of degree one is exactly transport of spherical functions. -/
theorem isUnramifiedBaseChangeHom_one_iff {b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r} :
    IsUnramifiedBaseChangeHom F E 1 r b ↔ b = sphericalHeckeFieldPullback F E e r := by
  have hPull : IsUnramifiedBaseChangeHom F E 1 r (sphericalHeckeFieldPullback F E e r) := by
    intro s ωF ωE hF hE
    rw [Eigenvalues.power_one] at hE
    apply IsSatakeCharacter.unique (s := s) _ hE
    intro i
    rw [AlgHom.comp_apply, sphericalHeckeFieldPullback_standard, hF i]
    simp only [standardHeckeScalar, PadicField.CanonicalTransport.residueCardinality_eq F E e]
  refine ⟨fun hb => ?_, fun h => h ▸ hPull⟩
  obtain ⟨f, _, hf⟩ := unramifiedBaseChangeHom.{u, v} p F E 1 r
  exact (hf b hb).trans (hf _ hPull).symm

end Langlands.BaseChange
