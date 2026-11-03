import Langlands.GroupScheme.Rational.CoordinateCotangentPairingProof
import Langlands.GroupScheme.Rational.CoordinateCotangentWeights
import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionProof
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Torus.ActionWeightDecomposition
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Equality of actual cotangent and Lie weight supports -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual cotangent pairing commutes with a change of coefficient algebra. -/
theorem kernelCotangentEquiv_naturality
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (X : Additive (lieKernel G A)) (q : Cotangent G) :
    kernelCotangentEquiv G B (lieKernelMapLinear G f X) q =
      f (kernelCotangentEquiv G A X q) := by
  obtain ⟨z, rfl⟩ := (augmentationIdeal G).toCotangent_surjective q
  exact Lie.kernelDerivationEquiv_naturality G f X.toMul z.val

/-- Evaluation against the actual Lie kernel detects every nonzero cotangent class. -/
theorem exists_kernelCotangentEquiv_ne_zero {q : Cotangent G} (hq : q ≠ 0) :
    ∃ X : Additive (lieKernel G k), kernelCotangentEquiv G k X q ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k hq
  exact ⟨(kernelCotangentEquiv G k).symm f, by simpa using hf⟩

/-- A nonzero ground-field scalar can be cancelled at every algebra-valued point. -/
theorem character_eq_of_scalar_mul_eq
    {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.toGrp.X.hom]
    {χ ψ : characterLattice S} {c : k} (hc : c ≠ 0)
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (s : Lie.AffinePoints S.toGrp A),
      (Lie.characterValue χ s : A) * algebraMap k A c =
        (Lie.characterValue ψ s : A) * algebraMap k A c) : χ = ψ := by
  apply CharacterUnits.unit_injective (G := S.toGrp)
  apply Units.ext
  have hu : IsUnit (algebraMap k (CharacterUnits.Coord S.toGrp) c) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap k (CharacterUnits.Coord S.toGrp))
  exact hu.mul_right_cancel (h (CharacterUnits.Coord S.toGrp)
    (CharacterUnits.universalPoint S.toGrp))

section LinearAlgebra

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {idx : Type*}

/-- A functional vanishing on a spanning family of submodules vanishes everywhere. -/
theorem linearMap_eq_zero_of_iSup_eq_top (p : idx → Submodule k W)
    (hp : iSup p = ⊤) (f : W →ₗ[k] k) (hf : ∀ i x, x ∈ p i → f x = 0) : f = 0 := by
  ext x
  apply Submodule.iSup_induction p (motive := fun y => f y = 0)
    (show x ∈ iSup p by rw [hp]; trivial)
  · exact hf
  · exact f.map_zero
  · intro y z hy hz
    rw [map_add, hy, hz, add_zero]

/-- Spanning weight families in perfect duality have the same nonzero support
when unequal labels pair to zero. -/
theorem supports_eq_of_orthogonal
    (e : V ≃ₗ[k] Module.Dual k W)
    (v : idx → Submodule k V) (w : idx → Submodule k W)
    (hv : iSup v = ⊤) (hw : iSup w = ⊤)
    (ho : ∀ i j, i ≠ j → ∀ X ∈ v i, ∀ q ∈ w j, e X q = 0) :
    {i | v i ≠ ⊥} = {i | w i ≠ ⊥} := by
  classical
  ext i
  constructor
  · intro hi hwi
    obtain ⟨X, hXi, hX⟩ := (Submodule.ne_bot_iff _).mp hi
    have hz : e X = 0 := linearMap_eq_zero_of_iSup_eq_top w hw (e X) (by
      intro j q hq
      by_cases hij : i = j
      · subst j
        rw [hwi] at hq
        simpa only [Submodule.mem_bot] using hq ▸ (e X).map_zero
      · exact ho i j hij X hXi q hq)
    exact hX (e.injective (hz.trans (e.map_zero).symm))
  · intro hi hvi
    obtain ⟨q, hqi, hq⟩ := (Submodule.ne_bot_iff _).mp hi
    apply hq
    apply (Module.forall_dual_apply_eq_zero_iff k q).mp
    intro f
    let X := e.symm f
    have hz : (LinearMap.applyₗ q).comp e.toLinearMap = 0 :=
      linearMap_eq_zero_of_iSup_eq_top v hv ((LinearMap.applyₗ q).comp e.toLinearMap) (by
        intro j Y hY
        change e Y q = 0
        by_cases hji : j = i
        · subst j
          rw [hvi] at hY
          rw [Submodule.mem_bot] at hY
          simp [hY]
        · exact ho j i hji Y hY q hqi)
    have hh := LinearMap.congr_fun hz X
    simpa [X] using hh

end LinearAlgebra

/-- The base-cotangent pairing on extended classes is the original cotangent pairing. -/
theorem kernelBaseCotangentEquiv_baseChange_eq
    {A : Type u} [CommRing A] [Algebra k A]
    (X : Additive (lieKernel G A)) (q : Cotangent G) :
    kernelBaseCotangentEquiv G A X (cotangentBaseChange q) =
      kernelCotangentEquiv G A X q := by
  obtain ⟨z, rfl⟩ := (augmentationIdeal G).toCotangent_surjective q
  exact kernelBaseCotangentEquiv_baseChange G A X z

/-- Unequal actual Lie and cotangent weights pair to zero under direct pullback. -/
theorem kernelCotangentEquiv_orthogonal
    {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.toGrp.X.hom]
    (b : AutomorphicAction S.toGrp G) {χ ψ : characterLattice S} (hχψ : χ ≠ ψ)
    {X : Additive (lieKernel G k)} (hX : X ∈ b.lieWeightSpace (𝟙 S.toGrp) χ)
    {q : Cotangent G} (hq : q ∈ cotangentWeightSpace b ψ) :
    kernelCotangentEquiv G k X q = 0 := by
  by_contra hc
  apply hχψ
  apply character_eq_of_scalar_mul_eq hc
  intro A _ _ s
  have hX' := hX A s
  simp only [Grp.id_hom_hom, Category.comp_id] at hX'
  have h := kernelBaseCotangentEquiv_action b s
    (lieKernelMapLinear G (Algebra.ofId k A) X) (cotangentBaseChange q)
  rw [hX', map_smul, LinearMap.smul_apply, hq A s, map_smul,
    kernelBaseCotangentEquiv_baseChange_eq, kernelCotangentEquiv_naturality] at h
  exact h

/-- Spanning of actual cotangent weights suffices for equality with intrinsic Lie support. -/
theorem cotangentSupport_eq_actionWeightSupport_of_iSup_eq_top
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (hS : IsSplitTorus S.toGrp)
    [LocallyOfFiniteType G.X.hom] (b : AutomorphicAction S.toGrp G)
    (hq : iSup (cotangentWeightSpace b) = ⊤) :
    cotangentSupport b = RelativeRoot.actionWeightSupport b ⊤ := by
  classical
  let := hS.isAffineHom
  have hlie := AutomorphicAction.isInternal_lieWeightSpace_of_isSplitTorus
    k G S hS b (𝟙 S.toGrp)
  have heq := supports_eq_of_orthogonal (kernelCotangentEquiv G k)
    (b.lieWeightSpace (𝟙 S.toGrp)) (cotangentWeightSpace b)
    hlie.submodule_iSup_eq_top hq (by
      intro χ ψ hχψ X hX q hq
      exact kernelCotangentEquiv_orthogonal b hχψ hX hq)
  ext χ
  have hsupport : χ ∈ RelativeRoot.actionWeightSupport b ⊤ ↔
      b.lieWeightSpace (𝟙 S.toGrp) χ ≠ ⊥ := by
    rw [RelativeRoot.mem_actionWeightSupport_iff,
      RelativeRoot.tangentSubmodule_top, inf_top_eq,
      RelativeRoot.actionWeightSpace_eq_lieWeightSpace]
  rw [hsupport]
  have hχ : b.lieWeightSpace (𝟙 S.toGrp) χ ≠ ⊥ ↔
      cotangentWeightSpace b χ ≠ ⊥ := Set.ext_iff.mp heq χ
  change (∃ q : Cotangent G, q ≠ 0 ∧ q ∈ cotangentWeightSpace b χ) ↔ _
  rw [hχ]
  constructor
  · rintro ⟨q, hq, hqχ⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨q, hqχ, hq⟩
  · intro h
    obtain ⟨q, hqχ, hq⟩ := (Submodule.ne_bot_iff _).mp h
    exact ⟨q, hq, hqχ⟩

/-- The support comparison follows from the actual coordinate decomposition. -/
theorem cotangentLieSupport_of_coordinateWeightDecomposition
    (hdec : CoordinateWeightDecompositionStatement.{u}) :
    CotangentLieSupportStatement.{u} := by
  intro k _ G hAff hft S hS b
  classical
  let := hAff
  let := hft
  exact cotangentSupport_eq_actionWeightSupport_of_iSup_eq_top hS b
    (hdec k G hAff S hS b).2.2.1.submodule_iSup_eq_top

/-- The exact actual cotangent and intrinsic Lie weight-support comparison. -/
theorem cotangentLieSupport : CotangentLieSupportStatement.{u} :=
  cotangentLieSupport_of_coordinateWeightDecomposition coordinateWeightDecomposition

end Langlands.GroupScheme.CoordinateWeights
