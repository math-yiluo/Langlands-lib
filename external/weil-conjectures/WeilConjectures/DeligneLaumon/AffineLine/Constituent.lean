/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.GeometricConstituent

/-!
# The trivial geometric constituent

Let `j : U₀ ↪ 𝔸¹_{k₀}` be a dense open immersion and `M` a lisse Weil sheaf on `U₀`. This file
collects the geometric facts behind the trivial linear character `ℒ_{ψ(0 · x)}` among the
geometric constituents of `M` (`AlgebraicGeometry.WeilSheaf.HasLinearArtinSchreierConstituent`
with `a = 0`).

- The geometric fiber `Ū = U₀ ⊗ k̄` is irreducible, as a nonempty open of the irreducible
  `𝔸¹_{k̄}` (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.irreducibleSpace_geometricFiber`).
- The geometric sheaf `ℒ_{ψ(0 · x)}|_Ū` is the constant sheaf `ℚ̄_ℓ`
  (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_iso_geometricConstituent_zero`):
  the multiplication by `0` factors through the Artin–Schreier map, `0 ^ q - 0 = 0`, and `ℒ_ψ`
  becomes trivial after pullback along the Artin–Schreier map.
- A geometrically constant `M` is constant on `Ū`
  (`exists_iso_biproduct_of_isGeometricallyConstant`), so a nonzero one has `ℚ̄_ℓ` as a
  quotient (`hasLinearArtinSchreierConstituent_zero_of_isGeometricallyConstant`), both in the
  namespace `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀] [Finite k₀]

omit [Finite k₀] in
/-- The geometric affine line `𝔸¹_{k̄}` is irreducible: it is the affine line over the integral
scheme `Spec k̄`. -/
instance irreducibleSpace_geometricFiber_affineLine :
    IrreducibleSpace (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
  have : IsIntegral (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (IsIntegral (Spec (.of (AlgebraicClosure k₀))))
  let e := (AffineSpace.isPullback_map (n := PUnit.{u + 1})
    (Scheme.specAlgebraicClosure k₀).hom).isoPullback
  exact Function.Surjective.irreducibleSpace (f := e.hom.homeomorph) e.hom.homeomorph.continuous
    e.hom.homeomorph.surjective

/-- The geometric multiplication by `0` factors through the geometric Artin–Schreier map:
`ĀS(0 · x) = 0 ^ q - 0 = 0 · x`. -/
lemma affineLine.geometricSMul_zero_comp_geometricArtinSchreierMap :
    affineLine.geometricSMul k₀ 0 ≫ affineLine.geometricArtinSchreierMap k₀ =
      affineLine.geometricSMul k₀ 0 := by
  have h : affineLine.geometricSMul k₀ 0 ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        AffineSpace.homOfVector
          ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
            (Scheme.specAlgebraicClosure k₀).hom) (fun _ ↦ 0) := by
    simp only [affineLine.geometricSMul, Scheme.Hom.geometricFiberProj]
    rw [pullback.lift_fst]
    simp
  apply pullback.hom_ext
  · change (_ ≫ affineLine.geometricArtinSchreierMap k₀) ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj = _ ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← Category.assoc,
      h]
    apply AffineSpace.hom_ext
    · simp [affineLine.artinSchreierMap]
    · intro i
      simp [affineLine.artinSchreierMap]
  · change (_ ≫ affineLine.geometricArtinSchreierMap k₀) ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = _ ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]

omit [Finite k₀] in
/-- The geometric multiplication by `0` absorbs the base change of a multiplication by
`a ∈ k₀`: `a · (0 · x) = 0 · x`. -/
lemma affineLine.geometricSMul_zero_comp_geometricFiberMap_smul (a : k₀) :
    affineLine.geometricSMul k₀ 0 ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ a)
      (comp_over (affineLine.smul k₀ a) _) = affineLine.geometricSMul k₀ 0 := by
  have h : affineLine.geometricSMul k₀ 0 ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
        AffineSpace.homOfVector
          ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
            (Scheme.specAlgebraicClosure k₀).hom) (fun _ ↦ 0) := by
    simp only [affineLine.geometricSMul, Scheme.Hom.geometricFiberProj]
    rw [pullback.lift_fst]
    simp
  apply pullback.hom_ext
  · change (_ ≫ Scheme.Hom.geometricFiberMap _ _) ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj = _ ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← Category.assoc,
      h]
    apply AffineSpace.hom_ext
    · simp [affineLine.smul]
    · intro i
      simp [affineLine.smul]
  · change (_ ≫ Scheme.Hom.geometricFiberMap _ _) ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = _ ≫
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]

end AffineLine

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

-- Instance search for the (co)kernels in the category of sheaves of modules is slow.
/-- The `ψ`-isotypic component `ℒ_ψ` of `AS_* ℚ̄_ℓ` becomes the constant sheaf `ℚ̄_ℓ` after
pullback along the geometric Artin–Schreier map: there the projector `e_ψ` factors as an
averaging map onto `ℚ̄_ℓ` followed by a split monomorphism (as in
`AlgebraicGeometry.WeilSheaf.isLisse_image_artinSchreierIdempotent`). -/
theorem WeilSheaf.nonempty_iso_upperStar_image_artinSchreierIdempotent
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].obj
      (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ≅
        ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  let Φ := ObjectProperty.ι (WeilSheaf.objectProperty k₀ l (affineLine k₀)) ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have := ObjectProperty.preservesKernels_ι _ (cokernel.π (WeilSheaf.artinSchreierIdempotent ψ))
  have := ObjectProperty.preservesCokernels_ι _ (WeilSheaf.artinSchreierIdempotent ψ)
  have : HasColimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have : HasLimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have hfac := affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ
    (Φ.map (WeilSheaf.artinSchreierIdempotent ψ))
    (affineLine.restriction_map_artinSchreierIdempotent ψ)
  have hab := affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ
  have : IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ) := ⟨⟨_, hab⟩⟩
  have : IsSplitMono (affineLine.artinSchreierSplitModHom l ψ) := ⟨⟨_, hab⟩⟩
  exact ⟨(affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].mapIso
    (Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫ Abelian.PreservesImage.iso Φ _ ≪≫
      Abelian.imageIsoImage _) ≪≫
    ((affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].mapIso (Abelian.imageIsoImage _).symm ≪≫
      Abelian.PreservesImage.iso _ _ ≪≫ Abelian.imageIsoImage _) ≪≫
      (image.isoStrongEpiMono _ _ hfac).symm⟩

/-- The geometric sheaf `ℒ_{ψ(0 · x)} = (0 ·)^* ℒ_{ψ(b x)}` is the constant sheaf `ℚ̄_ℓ`: the
multiplication by `0` absorbs the multiplication by `b` and factors through the geometric
Artin–Schreier map, along which `ℒ_ψ` becomes constant. -/
theorem WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : k₀) :
    Nonempty ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj (artinSchreier ψ b).obj.carrier ≅
        ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_upperStar_image_artinSchreierIdempotent (l := l) ψ
  let z := affineLine.geometricSMul k₀ 0
  let m := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ b)
      (comp_over (affineLine.smul k₀ b) (Spec (CommRingCat.of k₀)))
  let L := (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier
  have e₁ : (z)^*ᵃ[l].obj ((m)^*ᵃ[l].obj L) ≅ (z ≫ m)^*ᵃ[l].obj L :=
    ((ProEtale.adicUpperStarComp l z m).app L).symm
  have e₂ : (z ≫ m)^*ᵃ[l].obj L ≅ (z ≫ affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].obj L :=
    (ProEtale.adicUpperStarCongr l
      ((affineLine.geometricSMul_zero_comp_geometricFiberMap_smul k₀ b).trans
        (affineLine.geometricSMul_zero_comp_geometricArtinSchreierMap k₀).symm)).app L
  have e₃ : (z ≫ affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].obj L ≅
      (z)^*ᵃ[l].obj ((affineLine.geometricArtinSchreierMap k₀)^*ᵃ[l].obj L) :=
    (ProEtale.adicUpperStarComp l z _).app L
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ (z)^*ᵃ[l].mapIso e ≪≫ ProEtale.adicUpperStarUnitIso l z⟩

namespace WeilSheaf.LisseOnDenseOpen

variable (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)

/-- The trivial linear character `ℒ_{ψ(0 · x)}|_Ū`, the target of the constituents in
`AlgebraicGeometry.WeilSheaf.HasLinearArtinSchreierConstituent` for `a = 0`, is the constant
sheaf `ℚ̄_ℓ` on `Ū`. -/
theorem nonempty_iso_geometricConstituent_zero :
    Nonempty ((Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].obj
      ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) ≅
        ProEtale.AdicSheaf.unit l (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  obtain ⟨e⟩ := nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l) ψ 1
  exact ⟨(Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].mapIso e ≪≫
    ProEtale.adicUpperStarUnitIso l _⟩

/-- A geometrically constant lisse sheaf on `U₀` is constant on the connected `Ū`: it is a
finite direct sum of copies of `ℚ̄_ℓ` there. -/
theorem exists_iso_biproduct_of_isGeometricallyConstant (hc : D.IsGeometricallyConstant) :
    ∃ n : ℕ, Nonempty (D.sheaf.obj.carrier ≅ ⨁ fun _ : Fin n ↦
      ProEtale.AdicSheaf.unit l (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  have := D.irreducibleSpace_geometricFiber
  let V : (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber.Opens := ⊤
  have : ConnectedSpace V := isConnected_iff_connectedSpace.1 (by
    rw [TopologicalSpace.Opens.coe_top]
    exact isConnected_univ)
  obtain ⟨n, ⟨e⟩⟩ := hc V this
  have : IsIso V.ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  exact ⟨n, ⟨(V.ι)^*ᵃ[l].preimageIso
    (e ≪≫ (ProEtale.AdicSheaf.freeUpperStarIso l (Fin n) V.ι).symm)⟩⟩

/-- A nonzero geometrically constant lisse sheaf has the trivial rank-one sheaf
`ℒ_{ψ(0 · x)} = ℚ̄_ℓ` as a geometric constituent: on the connected `Ū` it is a nonzero finite
sum of copies of `ℚ̄_ℓ`, which surjects onto `ℒ_{ψ(0 · x)}|_U = ℚ̄_ℓ`. -/
theorem hasLinearArtinSchreierConstituent_zero_of_isGeometricallyConstant
    (hne : ¬ IsZero D.sheaf) (hc : D.IsGeometricallyConstant) :
    D.sheaf.HasLinearArtinSchreierConstituent ψ 0 D.j := by
  obtain ⟨n, ⟨e⟩⟩ := D.exists_iso_biproduct_of_isGeometricallyConstant hc
  obtain ⟨eT⟩ := D.nonempty_iso_geometricConstituent_zero ψ
  have hn : n ≠ 0 := by
    rintro rfl
    refine hne (isZero_iff_isZero_carrier.2 (IsZero.of_iso ?_ e))
    exact ⟨fun _ ↦ ⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩,
      fun _ ↦ ⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩
  exact ⟨_, 𝟙 _, e.hom ≫ biproduct.π _ ⟨0, Nat.pos_of_ne_zero hn⟩ ≫ eT.inv, D.lisse,
    inferInstance, inferInstance⟩

/-- **A trivial geometric constituent forces geometric constancy.** If the trivial rank-one
sheaf `ℒ_{ψ(0 · x)} = ℚ̄_ℓ` is a geometric constituent of an irreducible lisse sheaf `M`, then
`M` is geometrically constant: this is the sheaf-theoretic Clifford theorem
`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_biproduct_unit` on the irreducible
`Ū`. -/
theorem isGeometricallyConstant_of_hasLinearArtinSchreierConstituent_zero
    (hD : D.sheaf.IsIrreducibleLisse) (h : D.sheaf.HasLinearArtinSchreierConstituent ψ 0 D.j) :
    D.IsGeometricallyConstant := by
  have := D.irreducibleSpace_geometricFiber
  obtain ⟨B, i, p, hB, hi, hp⟩ := h
  obtain ⟨eT⟩ := D.nonempty_iso_geometricConstituent_zero ψ
  obtain ⟨n, ⟨e⟩⟩ := hD.exists_iso_biproduct_unit hB i (p ≫ eT.hom)
  intro V _
  exact ⟨n, ⟨(V.ι)^*ᵃ[l].mapIso e ≪≫ ProEtale.AdicSheaf.freeUpperStarIso l (Fin n) V.ι⟩⟩

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
