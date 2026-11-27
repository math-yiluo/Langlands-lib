import Langlands.Group.GL.BlockDeterminant
import Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredient
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientProof
import Langlands.AllFieldBZ.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist

/-!
# All-field port of `Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist`

Smooth dual and determinant-character twist of normalized block products, and
the dual twist `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` of a two-block supercuspidal product.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear

universe uF uV

private theorem determinant_leviEmbedding {R : Type uF} [CommRing R]
    {n : ℕ} (B : BlockShape n) (m : B.Levi R) :
    determinant (B.leviEmbedding R m) = ∏ i, determinant (m i) := by
  simpa only [BlockShape.leviInParabolic_val, BlockShape.leviProjection_section] using
    Langlands.GeneralLinear.determinant_blockParabolic B (B.leviInParabolic R m)

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

namespace ProductDualTwist

/-- The smooth dual of a normalized product of admissible blocks is the
normalized product of the block smooth duals. -/
theorem productSmoothDual {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hadm : letI := T.topology; ∀ i, IsAdmissible (δ i).representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    Nonempty (Representation.Equiv
      (smoothContragredient ((T.normalizedProductInductionFunctor B).obj δ).representation)
      ((T.normalizedProductInductionFunctor B).obj (fun i =>
        SmoothRep.of (smoothContragredient (δ i).representation)
          (isSmooth_smoothContragredient (δ i).representation))).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  let := T.leviTopologicalGroup B
  let τ := fun i => (δ i).representation
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor τ)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external τ hadm
  obtain ⟨EI, -⟩ := Langlands.AllFieldBZ.Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap τ) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ τ,
      FiniteTensor.smoothDualTensorMap_surjective τ hadm
      (fun i => Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T (B.size i))⟩
  let e2 : (FiniteTensor.external (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (FiniteTensor.external τ)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner τ).isIntertwining'
  exact ⟨(EI σ hσ).trans (T.normalizedParabolicInducedEquiv B e2.symm)⟩

private theorem blockTensor_determinant_twist {n : ℕ} (B : BlockShape n)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i)) =
      twist ((χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier))
        (B.blockTensor σ) := by
  let := T.topology
  let χL : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨(χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier),
      χ.isOpen_ker.preimage ((T.generalLinearDeterminant n).continuous.comp
        (T.blockLeviEmbedding B).continuous)⟩
  have hcoord (i : Fin B.length) :
      (χL.coordinate i).toMonoidHom = χ.toMonoidHom.comp
        (determinant : GeneralLinear (B.size i) F.Carrier →* F.Carrierˣ) := by
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom (determinant (B.leviEmbedding F.Carrier (Pi.mulSingle i g))) =
      χ.toMonoidHom (determinant g)
    rw [Langlands.AllFieldBZ.Classification.determinant_leviEmbedding]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  simpa only [hcoord] using χL.external_coordinate_twist σ

/-- A smooth determinant character `χ ∘ det` commutes with normalized block
products: `χ · i(δ_1, …, δ_r) ≅ i(χ δ_1, …, χ δ_r)`. -/
theorem productCharacterTwist {n : ℕ} (B : BlockShape n)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty (Representation.Equiv
      (twist (χ.toMonoidHom.comp determinant)
        ((T.normalizedProductInductionFunctor B).obj δ).representation)
      ((T.normalizedProductInductionFunctor B).obj (fun i =>
        (δ i).twist (χ.toMonoidHom.comp determinant)
          (χ.isOpen_ker.preimage
            (T.generalLinearDeterminant (B.size i)).continuous))).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let σ := fun i => (δ i).representation
  let χn : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) :=
    ⟨χ.toMonoidHom.comp determinant,
      χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous⟩
  let ρ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
  have hρ : IsSmooth ρ := by
    apply (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
    apply isSmooth_comp _ (T.blockLeviProjection B).continuous
    exact FiniteTensor.isSmooth_external σ (fun i => (δ i).isSmooth)
  obtain ⟨e, _⟩ := (Induction.inductionTwist (B.parabolic F.Carrier) χn ρ hρ).1
  let τ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
      (B.leviProjection F.Carrier))
  have hτ : twist (χn.toMonoidHom.comp (B.parabolic F.Carrier).subtype) ρ = τ := by
    dsimp only [τ]
    rw [blockTensor_determinant_twist F T B χ σ]
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (χ.toMonoidHom (determinant g.val) : ℂ) •
        ((T.parabolicHalfModulus B g : ℂ) • B.blockTensor σ (B.leviProjection F.Carrier g) v) =
      (T.parabolicHalfModulus B g : ℂ) •
        ((χ.toMonoidHom (determinant
          (B.leviEmbedding F.Carrier (B.leviProjection F.Carrier g))) : ℂ) •
            B.blockTensor σ (B.leviProjection F.Carrier g) v)
    rw [Langlands.GeneralLinear.determinant_blockParabolic, Langlands.AllFieldBZ.Classification.determinant_leviEmbedding]
    exact smul_comm _ _ _
  exact ⟨e.trans (Induction.smoothInducedEquiv _ (equivOfRepresentationEq hτ))⟩

/-- The smooth character `ν = |·|` of `F^×`, with the residue-normalized
absolute value; composed with the determinant it is `|det|`. -/
def absCharacter : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ⟨realPowerCharacter T.normalizedAbsUnits 1,
    Subgroup.isOpen_mono (ker_le_realPowerCharacter_ker _ 1) T.isOpen_ker_normalizedAbsUnits⟩

/-- `ν · i(δ_1, …, δ_r)~ ≅ i(ν δ_1~, …, ν δ_r~)` for admissible blocks, with
`ν = |det|` on each general linear group. -/
theorem productDualTwist {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hadm : letI := T.topology; ∀ i, IsAdmissible (δ i).representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    Nonempty (Representation.Equiv
      (twist (T.determinantPowerCharacter n 1)
        (smoothContragredient ((T.normalizedProductInductionFunctor B).obj δ).representation))
      ((T.normalizedProductInductionFunctor B).obj (fun i =>
        (δ i).contragredient.twist (T.determinantPowerCharacter (B.size i) 1)
          (T.isOpen_ker_determinantPowerCharacter (B.size i) 1))).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  obtain ⟨e1⟩ := productSmoothDual F T B δ hadm
  obtain ⟨e2⟩ := productCharacterTwist F T B (absCharacter F T) (fun i => (δ i).contragredient)
  exact ⟨(twistEquiv _ e1).trans e2⟩

/-- The supercuspidal representation `ν ρ~` of `GL_k`. -/
def dualTwist {k : ℕ}
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup k
  SupercuspidalRep.twist (T.determinantPowerCharacter k 1)
    (T.isOpen_ker_determinantPowerCharacter k 1)
    (T.ker_determinant_le_ker_determinantPowerCharacter k 1)
    (SupercuspidalRep.contragredient (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T k)
      (T.supercuspidalContragredientClosed Langlands.GeneralLinear.supercuspidalContragredient_allFieldBZ.{uF, uV} k) ρ)

/-- `ν · (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` for supercuspidal `ρ` of `GL_k` and `ρ'` of
`GL_l`, in the same block order. -/
theorem twoBlockDualTwist {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + l)
    Nonempty (Representation.Equiv
      (twist (T.determinantPowerCharacter (k + l) 1)
        (smoothContragredient ((T.normalizedProductInductionFunctor
          (Shahidi.twoBlocks k l hk hl)).obj (Langlands.Classification.twoBlockFactors hk hl ρ.obj ρ'.obj)).representation))
      ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
        (Langlands.Classification.twoBlockFactors hk hl (dualTwist F T ρ).obj (dualTwist F T ρ').obj)).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + l)
  let B := Shahidi.twoBlocks k l hk hl
  have hadm : ∀ i, IsAdmissible (Langlands.Classification.twoBlockFactors hk hl ρ.obj ρ'.obj i).representation := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact ρ.property.2.1
    · exact ρ'.property.2.1
  obtain ⟨e⟩ := productDualTwist F T B (Langlands.Classification.twoBlockFactors hk hl ρ.obj ρ'.obj) hadm
  have hfam : (fun i => letI := T.generalLinearTopologicalGroup (B.size i)
      (Langlands.Classification.twoBlockFactors hk hl ρ.obj ρ'.obj i).contragredient.twist
        (T.determinantPowerCharacter (B.size i) 1)
        (T.isOpen_ker_determinantPowerCharacter (B.size i) 1)) =
      Langlands.Classification.twoBlockFactors hk hl (dualTwist F T ρ).obj (dualTwist F T ρ').obj := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl
  rw [← hfam]
  exact ⟨e⟩

end ProductDualTwist

end Langlands.AllFieldBZ.Classification
