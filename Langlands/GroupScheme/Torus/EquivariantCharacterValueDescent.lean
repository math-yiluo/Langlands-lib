import Langlands.GroupScheme.Lie.RootOrbitCharacterAction
import Langlands.GroupScheme.AlgebraicGaloisPointDescent
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.SplittingAssembly

/-!
# Galois descent of torus points with prescribed character values

Let `L / k` be a Galois extension (not necessarily finite) and `T` a commutative group scheme
over `k` whose base change `T_L` is a split torus. Every Galois-equivariant homomorphism
`φ : X^*(T_L) → Lˣ` is the evaluation of the characters at some `k`-point of `T`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace EquivariantCharacterValueDescent

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_L" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L)) T

/-- The coefficient map `σ⁻¹`, as an `L`-algebra map out of the twisted test algebra. -/
def galoisTestInverse (σ : L ≃ₐ[k] L) : Lie.GaloisTestAlgebra σ L →ₐ[L] L where
  toRingHom := (σ.symm.toRingHom : L →+* L)
  commutes' c := σ.symm_apply_apply c

/-- The `L`-point of `T_L` corresponding to the conjugate of `s` by `σ⁻¹`. -/
def inverseConjugate (σ : L ≃ₐ[k] L) (s : Lie.AffinePoints (T_L).toGrp L) :
    Lie.AffinePoints (T_L).toGrp L :=
  Lie.affineMap (T_L).toGrp (galoisTestInverse k L σ)
    (Lie.galoisTestPoint k L σ L T.toGrp s)

/-- Over the original base, `inverseConjugate σ` is the coefficient action of `σ⁻¹`. -/
theorem affineBaseChangeEquiv_inverseConjugate (σ : L ≃ₐ[k] L)
    (s : Lie.AffinePoints (T_L).toGrp L) :
    Lie.affineBaseChangeEquiv k L T.toGrp L (inverseConjugate k L T σ s) =
      GaloisPoint.conjugate k L T.toGrp σ.symm
        (Lie.affineBaseChangeEquiv k L T.toGrp L s) := by
  change Lie.affineBaseChangeEquiv k L T.toGrp L
      (Lie.affineMap ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp)
        (galoisTestInverse k L σ) (Lie.galoisTestPoint k L σ L T.toGrp s)) = _
  rw [Lie.affineBaseChangeEquiv_naturality, Lie.affineBaseChangeEquiv_galoisTestPoint]
  rfl

/-- The character values of `inverseConjugate σ s` are `σ⁻¹` of the values of the
Galois-transported characters at `s`. -/
theorem characterValue_inverseConjugate (σ : L ≃ₐ[k] L)
    (χ : characterLattice T_L) (s : Lie.AffinePoints (T_L).toGrp L) :
    (Lie.characterValue χ (inverseConjugate k L T σ s) : L) =
      σ.symm (Lie.characterValue (characterLattice.galoisRepresentation k L T σ χ) s : L) := by
  rw [inverseConjugate, CoordinateWeights.characterValue_affineMap,
    Lie.characterValue_galoisRepresentation]
  rfl

variable {k L T}

/-- The affine character value is the point-character evaluation transported through
`Γ(Spec L) ≅ L`. -/
theorem characterValue_eq_pointCharacters (χ : characterLattice T_L)
    (s : Lie.AffinePoints (T_L).toGrp L) :
    Lie.characterValue χ s =
      Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
        (characterLattice.pointCharacters T_L _ s (.ofAdd χ)) := rfl

/-- Characters separate the `L`-points of a split torus. -/
theorem eq_of_characterValue_eq (hT : IsSplitTorus (T_L).toGrp)
    {s s' : Lie.AffinePoints (T_L).toGrp L}
    (h : ∀ χ : characterLattice T_L, Lie.characterValue χ s = Lie.characterValue χ s') :
    s = s' := by
  apply (characterLattice.pointCharacters_bijective T_L hT _).injective
  apply MonoidHom.ext
  intro χ
  have hχ := h χ.toAdd
  rw [characterValue_eq_pointCharacters, characterValue_eq_pointCharacters] at hχ
  apply Units.ext
  have hv := congrArg (fun u : Lˣ => (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (u : L)) hχ
  simpa using hv

/-- On a split torus, every homomorphism from the characters to `Lˣ` is the evaluation at
some `L`-point. -/
theorem exists_characterValue_eq (hT : IsSplitTorus (T_L).toGrp)
    (φ : characterLattice T_L →+ Additive Lˣ) :
    ∃ t : Lie.AffinePoints (T_L).toGrp L,
      ∀ χ : characterLattice T_L, Lie.characterValue χ t = (φ χ).toMul := by
  let ψ : Multiplicative (characterLattice T_L) →*
      (Γ(((algSpec (CommRingCat.of L)).obj
        (op (CommAlgCat.of (CommRingCat.of L) L))).left, ⊤))ˣ :=
    { toFun := fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom.toMonoidHom
        (φ χ.toAdd).toMul
      map_one' := by simp
      map_mul' := fun χ ψ => by simp }
  refine ⟨(characterLattice.pointCharactersEquiv T_L hT _).symm ψ, fun χ => ?_⟩
  rw [characterValue_eq_pointCharacters]
  have hψ : characterLattice.pointCharacters T_L _
      ((characterLattice.pointCharactersEquiv T_L hT _).symm ψ) =
        ψ := (characterLattice.pointCharactersEquiv T_L hT _).apply_symm_apply ψ
  rw [hψ]
  apply Units.ext
  simp [ψ]

end EquivariantCharacterValueDescent

open EquivariantCharacterValueDescent in
/-- **Galois descent of torus points with prescribed character values.** For a field `k`,
a Galois extension `L / k` (not necessarily finite) and a commutative group scheme `T` over
`k` whose base change `T_L` is a split torus, every homomorphism `φ : X^*(T_L) → Lˣ` that is
equivariant for the Galois action on characters is the evaluation of characters at a
`k`-point `h` of `T`: `χ (h_L) = φ χ` for every `χ`. -/
theorem exists_rationalPoint_characterValue_eq_of_equivariant
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp))
    (φ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T) →+
        Additive Lˣ)
    (hφ : ∀ (σ : L ≃ₐ[k] L)
        (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)),
      (((φ (characterLattice.galoisRepresentation k L T σ χ)).toMul : Lˣ) : L) =
        σ (((φ χ).toMul : Lˣ) : L)) :
    ∃ h : Lie.AffinePoints T.toGrp k,
      ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T),
        Lie.characterValue χ (rationalBaseChangePoint k L T h) = (φ χ).toMul := by
  have : IsAffine T.toGrp.X.left :=
    SplittingAssembly.isAffine_of_isTorus T.toGrp ⟨L, inferInstance, inferInstance, hT⟩
  obtain ⟨t, ht⟩ := exists_characterValue_eq hT φ
  let x := Lie.affineBaseChangeEquiv k L T.toGrp L t
  have hfix : ∀ σ : L ≃ₐ[k] L, inverseConjugate k L T σ t = t := by
    intro σ
    apply eq_of_characterValue_eq hT
    intro χ
    apply Units.ext
    rw [characterValue_inverseConjugate, ht, ht, hφ, AlgEquiv.symm_apply_apply]
  have hx : x ∈ GaloisPoint.fixedSubgroup k L T.toGrp := by
    intro σ
    have h := affineBaseChangeEquiv_inverseConjugate k L T σ.symm t
    rw [hfix, AlgEquiv.symm_symm] at h
    exact h.symm
  refine ⟨(GaloisPoint.algebraicFixedEquiv k L T.toGrp).symm ⟨x, hx⟩, fun χ => ?_⟩
  have hext := GaloisPoint.extend_algebraicFixedEquiv_symm k L T.toGrp ⟨x, hx⟩
  have hpt : rationalBaseChangePoint k L T
      ((GaloisPoint.algebraicFixedEquiv k L T.toGrp).symm ⟨x, hx⟩) = t := by
    apply (Lie.affineBaseChangeEquiv k L T.toGrp L).injective
    rw [affineBaseChangeEquiv_rationalBaseChangePoint]
    exact hext
  rw [hpt, ht]

end Langlands.GroupScheme
