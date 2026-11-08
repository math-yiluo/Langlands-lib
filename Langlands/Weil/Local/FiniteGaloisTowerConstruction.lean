import Langlands.Weil.Local.FiniteGaloisTower
import Langlands.Weil.Local.IntermediateWeil

/-! # Tower embeddings into finite Galois intermediate fields of the closure -/

noncomputable section

namespace Langlands.Weil.Local.FiniteGaloisTower

universe u

open LocalClassField ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F E : PadicField.{u} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (L₀ : FiniteIntermediateExtension F.Carrier)

local notation "LP" => L₀.asPadicField (p := p)

local instance finiteGaloisTowerConstructionAlgebra : Algebra (Padic p) L₀.field := (LP).algebra

/-- A Galois element of `F` preserves a normal intermediate field. -/
theorem absoluteGalois_mem_of_normal [Normal F.Carrier L₀.field]
    (σ : Field.absoluteGaloisGroup F.Carrier) {x : AlgebraicClosure F.Carrier}
    (hx : x ∈ L₀.field) : AlgEquiv.toAlgHom σ x ∈ L₀.field :=
  (IntermediateField.normal_iff_forall_map_le'.mp inferInstance σ) ⟨x, hx, rfl⟩

variable [Normal F.Carrier L₀.field]
  (hEL : extensionIntermediateField F E f ≤ L₀.field)

/-- The embedding `E → L₀` given by the corrected image of `E` in the closure. -/
def towerFieldEmbedding : E.Carrier →ₐ[Padic p] (LP).Carrier where
  toFun z := ⟨AlgEquiv.toAlgHom (intermediateClosureCorrection F L₀)
      (extensionFieldEmbedding F E f z),
    absoluteGalois_mem_of_normal F L₀ _
      (hEL ((mem_extensionIntermediateField F E f _).mpr ⟨z, rfl⟩))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' c := by
    apply Subtype.ext
    change AlgEquiv.toAlgHom (intermediateClosureCorrection F L₀)
        (extensionFieldEmbedding F E f (algebraMap (Padic p) E.Carrier c)) = _
    rw [← f.commutes, extensionFieldEmbedding_comp]
    exact (intermediateClosureCorrection F L₀).commutes _

/-- On `F` the tower embedding is the literal inclusion of `F` into `L₀`. -/
theorem towerFieldEmbedding_comp :
    (towerFieldEmbedding F E f L₀ hEL).comp f = intermediateEmbedding F L₀ := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change AlgEquiv.toAlgHom (intermediateClosureCorrection F L₀)
    (extensionFieldEmbedding F E f (f x)) = _
  rw [extensionFieldEmbedding_comp]
  exact (intermediateClosureCorrection F L₀).commutes x

/-- The published embedding of `L₀` extends that of `E` (hypothesis `hF1` of the tower theorem). -/
theorem towerFieldEmbedding_hF1 (z : E.Carrier) :
    extensionFieldEmbedding F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
        (towerFieldEmbedding F E f L₀ hEL z) = extensionFieldEmbedding F E f z := by
  rw [towerFieldEmbedding_comp]
  apply (intermediateClosureCorrection F L₀).injective
  change AlgEquiv.toAlgHom (intermediateClosureCorrection F L₀)
      (extensionFieldEmbedding F LP (intermediateEmbedding F L₀)
        (towerFieldEmbedding F E f L₀ hEL z)) =
    AlgEquiv.toAlgHom (intermediateClosureCorrection F L₀) (extensionFieldEmbedding F E f z)
  rw [intermediateClosureCorrection_fieldEmbedding]
  rfl

omit [Normal F.Carrier L₀.field] in
/-- The algebra given by the literal inclusion is the intermediate-field algebra. -/
theorem extensionAlgebra_intermediateEmbedding :
    extensionAlgebra F LP (intermediateEmbedding F L₀) =
      (inferInstance : Algebra F.Carrier L₀.field) :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- `L₀` is Galois over `F` for the algebra given by the tower embedding. -/
theorem towerFieldEmbedding_isGalois [hL : IsGalois F.Carrier L₀.field] :
    letI := extensionAlgebra F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
    IsGalois F.Carrier (LP).Carrier := by
  rw [towerFieldEmbedding_comp, extensionAlgebra_intermediateEmbedding]
  exact hL

/-- The tower inflation theorem for an intermediate field `L₀ ⊇ E` of the closure of `F`,
with the tower embedding `towerFieldEmbedding`. -/
theorem relativeInflation_finiteGaloisClass_of_le
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    [IsGalois F.Carrier L₀.field]
    (eE : LocalFactor.RankOne.ReciprocityCandidate E)
    (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (eL : LocalFactor.RankOne.ReciprocityCandidate LP)
    (heL : GeometricWeilReciprocityRelation LP (LP).canonicalTopologicalData eL)
    (hT : ExtensionWeilTransferReciprocityStatement.{u, u}) :
    letI := extensionAlgebra F E f
    letI := extensionAlgebra F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
    letI := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL)
    letI : IsScalarTower F.Carrier E.Carrier (LP).Carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := hE
    relativeInflation F.Carrier E.Carrier (LP).Carrier 2 (finiteGaloisClass F E f hE eE heE) =
      Module.finrank E.Carrier (LP).Carrier •
        finiteGaloisClass F LP ((towerFieldEmbedding F E f L₀ hEL).comp f)
          (towerFieldEmbedding_isGalois F E f L₀ hEL) eL heL :=
  relativeInflation_finiteGaloisClass F E LP f (towerFieldEmbedding F E f L₀ hEL) hE
    (towerFieldEmbedding_isGalois F E f L₀ hEL) (towerFieldEmbedding_hF1 F E f L₀ hEL)
    eE heE eL heL hT

end Langlands.Weil.Local.FiniteGaloisTower
