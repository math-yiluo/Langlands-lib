/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual
public import WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!
# The inverse transform of a punctual sheaf, geometrically

Let `G` be a Weil sheaf of finite support on the dual affine line. Its transform is
`FT_ψ(G) ≅ (π_*(i'^*𝓚_ψ ⊗ q^* i^* G))[1]`
(`AlgebraicGeometry.WeilSheaf.nonempty_iso_fourierTransform_toComplex_of_isPullback`), where
`i : Z₀ ↪ 𝔸¹` is a finite reduced closed subscheme containing the support, `X' = Z₀ × 𝔸¹` and
`π : X' ⟶ 𝔸¹` the projection. After base change to `k̄`, `Z̄` is a finite disjoint union of
points `ξ`, `X̄'` is a disjoint union of horizontal lines `{ξ} × 𝔸¹`, and on such a line the
kernel `μ^*ℒ_ψ` restricts to `ℒ_{ψ(ξ x)}`. Hence the underlying geometric sheaf of the transform
is a finite direct sum of geometric linear characters (blueprint
`proposition-fourier-transform-middle-extension--1`, Step 2).

Consequently the transform of an irreducible middle extension `(j_*M)[1]` is never punctual when
`M` has no linear character as a geometric constituent (Step 3): by Fourier inversion,
`(j_*M)[1](-1) ≅ FT_{ψ⁻¹}(G)`, so `M_k̄` is a direct sum of restrictions of linear characters.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_epi_carrier_lowerStar_tensorObj_fourierKernel_inv`: the
  geometric sheaf `πg_*(i'^*𝓚_{ψ⁻¹} ⊗ q^*E)`, if nonzero, surjects onto some `ℒ_{ψ(a x)}`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_hasLinearArtinSchreierConstituent_of_iso`:
  if `FT_ψ((j_*M)[1])` is a sheaf of finite support, then `M` has a geometric constituent
  `ℒ_{ψ(a x)}|_U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- **Pushforward along a trivial covering.** If `p : P ⟶ X` is separated with finitely many
sections `σ k` inducing an isomorphism `∐ₖ X ≅ P`, then `p_* F ≅ ⨁ₖ (σ k)^* F`. -/
theorem nonempty_adicLowerStar_iso_biproduct_of_isIso_sigmaDesc {X P : Scheme.{u}} {κ : Type}
    [Finite κ] (σ : κ → (X ⟶ P)) (p : P ⟶ X) [IsSeparated p] (hσ : ∀ k, σ k ≫ p = 𝟙 X)
    [IsIso (Sigma.desc σ)] (F : AdicSheaf l P) :
    Nonempty ((p)_*ᵃ[l].obj F ≅ ⨁ fun k ↦ (σ k)^*ᵃ[l].obj F) := by
  have (k : κ) : IsClosedImmersion (σ k) := by
    have : IsClosedImmersion (σ k ≫ p) := by
      rw [hσ]
      infer_instance
    exact IsClosedImmersion.of_comp (σ k) p
  exact ⟨(p)_*ᵃ[l].mapIso (@asIso _ _ _ _ _
      (isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit_of_cover σ
        (pairwise_disjoint_range_of_isIso_sigmaDesc σ)
        (exists_mem_range_of_isIso_sigmaDesc σ) F)) ≪≫
      (p)_*ᵃ[l].mapBiproduct _ ≪≫
      biproduct.mapIso fun k ↦ (adicLowerStarComp l (σ k) p).app _ ≪≫
        (adicLowerStarCongr l (hσ k)).app _ ≪≫ (adicLowerStarId l X).app _⟩

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- The coordinate in `k̄` of a geometric point `t : Spec k̄ ⟶ 𝔸¹` of the affine line. -/
noncomputable def affineLine.coordOfPoint (t : Spec (.of (AlgebraicClosure k₀)) ⟶ affineLine k₀) :
    AlgebraicClosure k₀ :=
  (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).hom.hom
    (t.appTop (AffineSpace.coord _ PUnit.unit))

omit [Finite k₀] in
/-- **The kernel along a horizontal line.** Let `i : Z ⟶ 𝔸¹` be a morphism over `k₀`, and
`X' = Z ×_{𝔸¹} (𝔸¹ × 𝔸¹)` its base change along the first projection, with projections `q` to
`Z` and `i'` to the plane. A section `σ` of the base change to `k̄` of `X' ⟶ 𝔸¹`
(the second projection) lying over the geometric point `t` of `Z` is `y ↦ (t, y)`; along it
the multiplication `μ` becomes the geometric multiplication by the coordinate of `t`. -/
lemma geometricFiberMap_mul_eq_geometricSMul {Z X' : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [i.IsOver (Spec (CommRingCat.of k₀))] (q : X' ⟶ Z)
    [q.IsOver (Spec (CommRingCat.of k₀))] (i' : X' ⟶ affinePlane k₀)
    [i'.IsOver (Spec (CommRingCat.of k₀))] (hw : i' ≫ affinePlane.fst k₀ = q ≫ i)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (σ : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (X' ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hσq : σ ≫ Scheme.Hom.geometricFiberMap q (comp_over q _) =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t)
    (hσπ : σ ≫ Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.snd k₀)
      (comp_over (i' ≫ affinePlane.snd k₀) _) = 𝟙 _) :
    σ ≫ Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.mul k₀)
      (comp_over (i' ≫ affinePlane.mul k₀) _) =
      affineLine.geometricSMul k₀ (affineLine.coordOfPoint
        (t ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)) := by
  have h₁ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫
      affinePlane.snd k₀ = (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := by
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj (i' ≫ affinePlane.snd k₀)
        (comp_over (i' ≫ affinePlane.snd k₀) _), ← Category.assoc, hσπ, Category.id_comp]
  have h₂ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫
      affinePlane.fst k₀ =
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t ≫
          (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i := by
    rw [hw, ← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc q (comp_over q _),
      ← Category.assoc σ, hσq, Category.assoc]
  have h₃ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure
      (i' ≫ affinePlane.snd k₀) (comp_over (i' ≫ affinePlane.snd k₀) _), ← Category.assoc, hσπ,
      Category.id_comp]
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      affineLine.geometricSMul_comp_geometricFiberProj, affinePlane.mul]
    simp only [← Category.assoc]
    rw [AffineSpace.comp_homOfVector]
    have key (g : affinePlane k₀ ⟶ affineLine k₀) (c : Γ(affineLine k₀, ⊤)) :
        ((σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) ≫ i').appTop (g.appTop c) =
          (σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫ g).appTop c := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      simp only [Category.assoc]
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_over,
        ← comp_over (affinePlane.snd k₀) (Spec (CommRingCat.of k₀))]
      simp only [Category.assoc]
      rw [reassoc_of% h₁,
        Scheme.Hom.geometricFiber_condition]
    · simp only [AffineSpace.homOfVector_appTop_coord, Function.comp_apply, map_mul]
      rw [key, key, h₁, h₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp [affineLine.coordOfPoint, affineLine.geometricConst]
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure, ← h₃]

namespace WeilSheaf

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The inverse transform of a punctual sheaf, geometrically, explicitly** (blueprint
`proposition-fourier-transform-middle-extension--1`, Step 2). In the situation of
`AlgebraicGeometry.WeilSheaf.exists_epi_carrier_lowerStar_tensorObj_fourierKernel_inv`, the
geometric sheaf underlying `π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^*E)` is a finite direct sum
`⨁ₖ ℒ_{ψ(-ξₖ x)}^{mₖ}` over the geometric points `tₖ` of `Z`, where `ξₖ` is the coordinate of
the image of `tₖ` in `𝔸¹`. -/
theorem exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) {Z X' : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] [X'.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [i.IsOver (Spec (CommRingCat.of k₀))]
    (q : X' ⟶ Z) [q.IsOver (Spec (CommRingCat.of k₀))]
    (i' : X' ⟶ affinePlane k₀) [i'.IsOver (Spec (CommRingCat.of k₀))]
    (π : X' ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact π]
    [QuasiSeparated π] [LocallyOfFiniteType π]
    (hπ : i' ≫ affinePlane.snd k₀ = π) (hw : i' ≫ affinePlane.fst k₀ = q ≫ i)
    (hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (E : WeilSheaf k₀ l Z) :
    ∃ (n : ℕ) (t : Fin n → (Spec (.of (AlgebraicClosure k₀)) ⟶
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)) (m : Fin n → ℕ),
      (∀ k, t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = 𝟙 _) ∧
      Nonempty (((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
          ((WeilSheaf.upperStar q).obj E)
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹)))).obj.carrier ≅
        ⨁ fun k ↦ ⨁ fun _ : Fin (m k) ↦ (affineLine.geometricSMul k₀ (-affineLine.coordOfPoint
          (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)))^*ᵃ[l].obj
            (artinSchreier ψ 1).obj.carrier) := by
  subst hπ
  obtain ⟨n, t, ht, hiso⟩ :=
    exists_isIso_sigmaDesc_geometricFiber_of_isFinite (Z ↘ Spec (CommRingCat.of k₀))
  have hπS : (i' ≫ affinePlane.snd k₀) ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) =
      X' ↘ Spec (CommRingCat.of k₀) := comp_over _ _
  have hqS : q ≫ Z ↘ Spec (CommRingCat.of k₀) = X' ↘ Spec (CommRingCat.of k₀) := hP.w.trans hπS
  have : IsFinite (i' ≫ affinePlane.snd k₀) := MorphismProperty.of_isPullback hP inferInstance
  have hP' : IsPullback (Scheme.Hom.geometricFiberMap q hqS)
      (Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.snd k₀) hπS)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    refine IsPullback.of_right (h₁₂ := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (h₂₂ := (Scheme.specAlgebraicClosure k₀).hom) (v₁₃ := Z ↘ Spec (CommRingCat.of k₀))
      ?_ (by simp) (IsPullback.of_hasPullback _ _)
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Scheme.Hom.geometricFiber_condition]
    exact (Scheme.Hom.isPullback_geometricFiberMap _ hπS).flip.paste_horiz hP
  have := FinitaryPreExtensive.isIso_sigmaDesc_isPullback_lift hP' t ht
  set σ : Fin n → ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (X' ↘ Spec (CommRingCat.of k₀)).geometricFiber) := fun k ↦
    hP'.lift ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t k)
      (𝟙 _) (by simp [ht])
  set H := ((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
    ((WeilSheaf.upperStar q).obj E)
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹))
  obtain ⟨e₁⟩ := ProEtale.nonempty_adicLowerStar_iso_biproduct_of_isIso_sigmaDesc σ
    (Scheme.Hom.geometricFiberMap _ hπS) (fun k ↦ hP'.lift_snd _ _ _) H.obj.carrier
  have hE : ProEtale.IsAdicLisseSheaf E.obj.carrier := isLisse_of_isFinite_of_isReduced E
  set U₁ := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have hk (k : Fin n) : ∃ m : ℕ,
      Nonempty ((σ k)^*ᵃ[l].obj H.obj.carrier ≅ ⨁ fun _ : Fin m ↦
        (affineLine.geometricSMul k₀ (-affineLine.coordOfPoint
          (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)))^*ᵃ[l].obj
            (artinSchreier ψ 1).obj.carrier) := by
    have : IsOpenImmersion (σ k) := ProEtale.isOpenImmersion_of_isIso_sigmaDesc σ k
    have hsq : σ k ≫ Scheme.Hom.geometricFiberMap q hqS =
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t k :=
      hP'.lift_fst _ _ _
    have hmul := geometricFiberMap_mul_eq_geometricSMul i q i' hw (t k) (σ k) hsq
      (hP'.lift_snd _ _ _)
    set b := affineLine.coordOfPoint
      (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)
    have hcomp : (σ k ≫ Scheme.Hom.geometricFiberMap i' (comp_over i' _)) ≫
        Scheme.Hom.geometricFiberMap (affineSpacePair.pairing PUnit.{u + 1} k₀)
          (comp_over (affineSpacePair.pairing PUnit.{u + 1} k₀) _) =
          affineLine.geometricSMul k₀ b := by
      rw [Category.assoc, ← Scheme.Hom.geometricFiberMap_comp]
      simpa only [affineSpacePair.pairing_punit] using hmul
    let ig := Scheme.Hom.geometricFiberMap i' (comp_over i' (Spec (CommRingCat.of k₀)))
    let mg := Scheme.Hom.geometricFiberMap (affineSpacePair.pairing PUnit.{u + 1} k₀)
      (comp_over (affineSpacePair.pairing PUnit.{u + 1} k₀) (Spec (CommRingCat.of k₀)))
    let A := (artinSchreier ψ⁻¹ 1).obj.carrier
    let Lc := (ig)^*ᵃ[l].obj ((mg)^*ᵃ[l].obj A)
    let eL : (σ k)^*ᵃ[l].obj Lc ≅ (affineLine.geometricSMul k₀ b)^*ᵃ[l].obj A :=
      ((ProEtale.adicUpperStarComp l (σ k) ig).app ((mg)^*ᵃ[l].obj A)).symm ≪≫
        ((ProEtale.adicUpperStarComp l (σ k ≫ ig) mg).app A).symm ≪≫
        (ProEtale.adicUpperStarCongr l hcomp).app A
    let eD : (σ k)^*ᵃ[l].obj ((ProEtale.AdicSheaf.ihom Lc).obj (ProEtale.AdicSheaf.unit l _)) ≅
        (ProEtale.AdicSheaf.ihom ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj
          (artinSchreier ψ⁻¹ 1).obj.carrier)).obj U₁ :=
      (ProEtale.adicUpperStarIhomIso l (σ k) Lc).app _ ≪≫
        (ProEtale.AdicSheaf.ihom _).mapIso (ProEtale.adicUpperStarUnitIso l (σ k)) ≪≫
        (Mod.ihomMapIso eL.symm).app U₁
    obtain ⟨m, ⟨eV⟩⟩ := (hE.upperStar (t k)).exists_iso_biproduct_of_isAlgClosed
    let toAC := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    let qg := Scheme.Hom.geometricFiberMap q hqS
    let Ec := E.obj.carrier
    let eE : (σ k)^*ᵃ[l].obj ((qg)^*ᵃ[l].obj Ec) ≅ ⨁ fun _ : Fin m ↦ U₁ :=
      ((ProEtale.adicUpperStarComp l (σ k) qg).app Ec).symm ≪≫
        (ProEtale.adicUpperStarCongr l hsq).app Ec ≪≫
        (ProEtale.adicUpperStarComp l toAC (t k)).app Ec ≪≫ (toAC)^*ᵃ[l].mapIso eV ≪≫
        (toAC)^*ᵃ[l].mapBiproduct _ ≪≫
        biproduct.mapIso fun _ ↦ ProEtale.adicUpperStarUnitIso l toAC
    obtain ⟨eA⟩ :=
      nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv (l := l) ψ b
    exact ⟨m, ⟨(ProEtale.adicUpperStarIhomIso l (σ k) _).app _ ≪≫
      (ProEtale.AdicSheaf.ihom _).mapIso eE ≪≫ (ProEtale.AdicSheaf.ihom _).mapBiproduct _ ≪≫
      biproduct.mapIso fun _ ↦ (Mod.ihomMapIso eD.symm).app U₁ ≪≫ eA⟩⟩
  choose m e using hk
  exact ⟨n, t, m, ht, ⟨e₁ ≪≫ biproduct.mapIso fun k ↦ (e k).some⟩⟩

/-- **The inverse transform of a punctual sheaf, geometrically** (blueprint
`proposition-fourier-transform-middle-extension--1`, Step 2). Let `i : Z₀ ⟶ 𝔸¹` be a finite reduced
`k₀`-scheme over the line and `X' = Z₀ × 𝔸¹`, with projections `q : X' ⟶ Z₀` and `π : X' ⟶ 𝔸¹` and
`i' = (i ∘ q, π) : X' ⟶ 𝔸¹ × 𝔸¹`. For a Weil sheaf `E` on `Z₀`, the geometric sheaf underlying
`π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^*E)` is, if nonzero, a quotient of some linear character `ℒ_{ψ(a x)}`
on `𝔸¹_{k̄}`: `Z̄` is a finite disjoint union of points `ξ`, so the sheaf is the direct sum of its
restrictions to the lines `{ξ} × 𝔸¹`, on which `i'^*𝓚_{ψ⁻¹}` is `ℒ_{ψ⁻¹(ξ x)}` and `q^*E` is
constant; and the tensor product `ℒ_{ψ⁻¹(ξ x)} ⊗ ℚ̄_ℓ = 𝓗om(ℒ_{ψ⁻¹(ξ x)}^∨, ℚ̄_ℓ)` is
`ℒ_{ψ(-ξ x)}`. -/
theorem exists_epi_carrier_lowerStar_tensorObj_fourierKernel_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) {Z X' : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] [X'.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [i.IsOver (Spec (CommRingCat.of k₀))]
    (q : X' ⟶ Z) [q.IsOver (Spec (CommRingCat.of k₀))]
    (i' : X' ⟶ affinePlane k₀) [i'.IsOver (Spec (CommRingCat.of k₀))]
    (π : X' ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact π]
    [QuasiSeparated π] [LocallyOfFiniteType π]
    (hπ : i' ≫ affinePlane.snd k₀ = π) (hw : i' ≫ affinePlane.fst k₀ = q ≫ i)
    (hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (E : WeilSheaf k₀ l Z)
    (h : ¬ IsZero ((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
          ((WeilSheaf.upperStar q).obj E)
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹)))).obj.carrier) :
    ∃ (a : AlgebraicClosure k₀) (p : ((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
          ((WeilSheaf.upperStar q).obj E)
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹)))).obj.carrier ⟶
        (affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier), Epi p := by
  subst hπ
  obtain ⟨n, t, ht, hiso⟩ :=
    exists_isIso_sigmaDesc_geometricFiber_of_isFinite (Z ↘ Spec (CommRingCat.of k₀))
  have hπS : (i' ≫ affinePlane.snd k₀) ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) =
      X' ↘ Spec (CommRingCat.of k₀) := comp_over _ _
  have hqS : q ≫ Z ↘ Spec (CommRingCat.of k₀) = X' ↘ Spec (CommRingCat.of k₀) := hP.w.trans hπS
  have : IsFinite (i' ≫ affinePlane.snd k₀) := MorphismProperty.of_isPullback hP inferInstance
  have hP' : IsPullback (Scheme.Hom.geometricFiberMap q hqS)
      (Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.snd k₀) hπS)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    refine IsPullback.of_right (h₁₂ := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (h₂₂ := (Scheme.specAlgebraicClosure k₀).hom) (v₁₃ := Z ↘ Spec (CommRingCat.of k₀))
      ?_ (by simp) (IsPullback.of_hasPullback _ _)
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Scheme.Hom.geometricFiber_condition]
    exact (Scheme.Hom.isPullback_geometricFiberMap _ hπS).flip.paste_horiz hP
  have := FinitaryPreExtensive.isIso_sigmaDesc_isPullback_lift hP' t ht
  set σ : Fin n → ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (X' ↘ Spec (CommRingCat.of k₀)).geometricFiber) := fun k ↦
    hP'.lift ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t k)
      (𝟙 _) (by simp [ht])
  set H := ((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
    ((WeilSheaf.upperStar q).obj E)
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹))
  obtain ⟨e₁⟩ := ProEtale.nonempty_adicLowerStar_iso_biproduct_of_isIso_sigmaDesc σ
    (Scheme.Hom.geometricFiberMap _ hπS) (fun k ↦ hP'.lift_snd _ _ _) H.obj.carrier
  have hE : ProEtale.IsAdicLisseSheaf E.obj.carrier := isLisse_of_isFinite_of_isReduced E
  set U₁ := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have hk (k : Fin n) : ∃ (m : ℕ) (a : AlgebraicClosure k₀),
      Nonempty ((σ k)^*ᵃ[l].obj H.obj.carrier ≅ ⨁ fun _ : Fin m ↦
        (affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) := by
    have : IsOpenImmersion (σ k) := ProEtale.isOpenImmersion_of_isIso_sigmaDesc σ k
    have hsq : σ k ≫ Scheme.Hom.geometricFiberMap q hqS =
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t k :=
      hP'.lift_fst _ _ _
    have hmul := geometricFiberMap_mul_eq_geometricSMul i q i' hw (t k) (σ k) hsq
      (hP'.lift_snd _ _ _)
    set b := affineLine.coordOfPoint
      (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)
    have hcomp : (σ k ≫ Scheme.Hom.geometricFiberMap i' (comp_over i' _)) ≫
        Scheme.Hom.geometricFiberMap (affineSpacePair.pairing PUnit.{u + 1} k₀)
          (comp_over (affineSpacePair.pairing PUnit.{u + 1} k₀) _) =
          affineLine.geometricSMul k₀ b := by
      rw [Category.assoc, ← Scheme.Hom.geometricFiberMap_comp]
      simpa only [affineSpacePair.pairing_punit] using hmul
    let ig := Scheme.Hom.geometricFiberMap i' (comp_over i' (Spec (CommRingCat.of k₀)))
    let mg := Scheme.Hom.geometricFiberMap (affineSpacePair.pairing PUnit.{u + 1} k₀)
      (comp_over (affineSpacePair.pairing PUnit.{u + 1} k₀) (Spec (CommRingCat.of k₀)))
    let A := (artinSchreier ψ⁻¹ 1).obj.carrier
    let Lc := (ig)^*ᵃ[l].obj ((mg)^*ᵃ[l].obj A)
    let eL : (σ k)^*ᵃ[l].obj Lc ≅ (affineLine.geometricSMul k₀ b)^*ᵃ[l].obj A :=
      ((ProEtale.adicUpperStarComp l (σ k) ig).app ((mg)^*ᵃ[l].obj A)).symm ≪≫
        ((ProEtale.adicUpperStarComp l (σ k ≫ ig) mg).app A).symm ≪≫
        (ProEtale.adicUpperStarCongr l hcomp).app A
    let eD : (σ k)^*ᵃ[l].obj ((ProEtale.AdicSheaf.ihom Lc).obj (ProEtale.AdicSheaf.unit l _)) ≅
        (ProEtale.AdicSheaf.ihom ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj
          (artinSchreier ψ⁻¹ 1).obj.carrier)).obj U₁ :=
      (ProEtale.adicUpperStarIhomIso l (σ k) Lc).app _ ≪≫
        (ProEtale.AdicSheaf.ihom _).mapIso (ProEtale.adicUpperStarUnitIso l (σ k)) ≪≫
        (Mod.ihomMapIso eL.symm).app U₁
    obtain ⟨m, ⟨eV⟩⟩ := (hE.upperStar (t k)).exists_iso_biproduct_of_isAlgClosed
    let toAC := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    let qg := Scheme.Hom.geometricFiberMap q hqS
    let Ec := E.obj.carrier
    let eE : (σ k)^*ᵃ[l].obj ((qg)^*ᵃ[l].obj Ec) ≅ ⨁ fun _ : Fin m ↦ U₁ :=
      ((ProEtale.adicUpperStarComp l (σ k) qg).app Ec).symm ≪≫
        (ProEtale.adicUpperStarCongr l hsq).app Ec ≪≫
        (ProEtale.adicUpperStarComp l toAC (t k)).app Ec ≪≫ (toAC)^*ᵃ[l].mapIso eV ≪≫
        (toAC)^*ᵃ[l].mapBiproduct _ ≪≫
        biproduct.mapIso fun _ ↦ ProEtale.adicUpperStarUnitIso l toAC
    obtain ⟨a, ⟨eA⟩⟩ :=
      exists_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv (l := l) ψ b
    exact ⟨m, a, ⟨(ProEtale.adicUpperStarIhomIso l (σ k) _).app _ ≪≫
      (ProEtale.AdicSheaf.ihom _).mapIso eE ≪≫ (ProEtale.AdicSheaf.ihom _).mapBiproduct _ ≪≫
      biproduct.mapIso fun _ ↦ (Mod.ihomMapIso eD.symm).app U₁ ≪≫ eA⟩⟩
  choose m a e using hk
  obtain ⟨k, hk⟩ : ∃ k, m k ≠ 0 := by
    by_contra! hall
    refine h ((IsZero.iff_id_eq_zero _).2 ?_)
    rw [← cancel_mono e₁.hom, zero_comp, Category.id_comp]
    refine biproduct.hom_ext _ _ fun k ↦ ?_
    refine IsZero.eq_of_tgt ((IsZero.iff_id_eq_zero _).2 ?_) _ _
    rw [← cancel_mono (e k).some.hom, zero_comp, Category.id_comp]
    exact biproduct.hom_ext _ _ fun j ↦ (Fin.cast (hall k) j).elim0
  exact ⟨a k, e₁.hom ≫ biproduct.π _ k ≫ (e k).some.hom ≫
    biproduct.π _ ⟨0, Nat.pos_of_ne_zero hk⟩, inferInstance⟩

namespace LisseOnDenseOpen

variable (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)

/-- **The geometric sheaf of the middle extension, by inversion.** If the transform of
`(j_*M)[1]` is a sheaf `G` placed in degree `0`, and `FT_{ψ⁻¹}(G)` is a sheaf `H` placed in degree
`-1`, then Fourier inversion `(j_*M)[1](-1) ≅ FT_{ψ⁻¹}(FT_ψ((j_*M)[1])) ≅ H[1]` shows that `j_*M`
and `H` have the same underlying geometric sheaf, the Tate twist being a constant twist. -/
theorem nonempty_carrier_directImage_iso_of_iso (hψ : ψ ≠ 1)
    {G H : WeilSheaf k₀ l (affineLine k₀)}
    (e : (fourierTransform ψ).obj D.middleExtension ≅ WeilSheaf.toComplex.obj G)
    (e₂ : (fourierTransform ψ⁻¹).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toShiftedComplex.obj H) :
    Nonempty (D.directImage.obj.carrier ≅ H.obj.carrier) := by
  obtain ⟨eInv⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ hψ
  let Φ := (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  let c₀ : Φ.obj ((WeilComplex.homologySheaf (-1)).obj D.middleExtension) ≅
      Φ.obj (((WeilComplex.homologySheaf (-1)).obj D.middleExtension).constantTwist
        (WeilSheaf.cyclotomicUnit k₀ l ^ (-1 : ℤ))) := Iso.refl _
  exact ⟨Φ.mapIso (WeilComplex.homologySheafShiftToComplexIso D.directImage 1 (-1)
      (by simp)).symm ≪≫ c₀ ≪≫
    Φ.mapIso (WeilComplex.homologySheafTateTwistIso (-1) (-1) D.middleExtension).symm ≪≫
    Φ.mapIso ((WeilComplex.homologySheaf (-1)).mapIso
      ((eInv.app _).symm ≪≫ (fourierTransform ψ⁻¹).mapIso e ≪≫ e₂)) ≪≫
    Φ.mapIso (WeilSheaf.toShiftedComplexCompHomologySheafIso.app H)⟩

/-- A quotient `ℒ_{ψ(a x)}` of the geometric sheaf of `j_*M` restricts to a quotient
`ℒ_{ψ(a x)}|_U` of `M_k̄`, since `j^* j_* M = M`: a linear geometric constituent of `M`. -/
theorem hasLinearArtinSchreierConstituent_of_epi {a : AlgebraicClosure k₀}
    (p : D.directImage.obj.carrier ⟶
      (affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) [Epi p] :
    D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j := by
  let jg := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  have := (ProEtale.adicUpperStarLowerStarAdjunction l jg).isLeftAdjoint
  let ΦU := (WeilSheaf.objectProperty k₀ l D.U).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l D.U)
  let cD : D.sheaf.obj.carrier ≅ (jg)^*ᵃ[l].obj D.directImage.obj.carrier :=
    ΦU.mapIso (upperStarDirectImageIso D.j D.sheaf).symm
  exact ⟨D.sheaf.obj.carrier, 𝟙 _, cD.hom ≫ (jg)^*ᵃ[l].map p, D.lisse,
    inferInstance, epi_comp' inferInstance (Functor.map_epi _ _)⟩

/-- If `j_*M` has zero underlying geometric sheaf, then `M = j^* j_* M` is zero. -/
theorem isZero_of_isZero_carrier_directImage (h : IsZero D.directImage.obj.carrier) :
    IsZero D.sheaf := by
  let jg := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  let ΦU := (WeilSheaf.objectProperty k₀ l D.U).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l D.U)
  let cD : D.sheaf.obj.carrier ≅ (jg)^*ᵃ[l].obj D.directImage.obj.carrier :=
    ΦU.mapIso (upperStarDirectImageIso D.j D.sheaf).symm
  have := (ProEtale.adicUpperStarLowerStarAdjunction l jg).isLeftAdjoint
  exact isZero_iff_isZero_carrier.2 (((jg)^*ᵃ[l].map_isZero h).of_iso cD)

/-- The punctual case of `proposition-fourier-transform-middle-extension--1`, Step 3, for an
explicit presentation `FT_{ψ⁻¹}(G) ≅ (π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^*E))[1]` of the inverse transform. -/
theorem exists_hasLinearArtinSchreierConstituent_of_iso_of_isPullback (hψ : ψ ≠ 1)
    (hD : ¬ IsZero D.sheaf) (G : WeilSheaf k₀ l (affineLine k₀))
    (e : (fourierTransform ψ).obj D.middleExtension ≅ WeilSheaf.toComplex.obj G)
    {Z X' : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] [X'.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [i.IsOver (Spec (CommRingCat.of k₀))]
    (q : X' ⟶ Z) [q.IsOver (Spec (CommRingCat.of k₀))]
    (i' : X' ⟶ affinePlane k₀) [i'.IsOver (Spec (CommRingCat.of k₀))]
    (π : X' ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact π]
    [QuasiSeparated π] [LocallyOfFiniteType π]
    (hπ : i' ≫ affinePlane.snd k₀ = π) (hw : i' ≫ affinePlane.fst k₀ = q ≫ i)
    (hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (E : WeilSheaf k₀ l Z)
    (e₂ : (fourierTransform ψ⁻¹).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toShiftedComplex.obj ((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj
          ((WeilSheaf.upperStar q).obj E)
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹))))) :
    ∃ a : AlgebraicClosure k₀, D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j := by
  obtain ⟨c⟩ := D.nonempty_carrier_directImage_iso_of_iso ψ hψ e e₂
  obtain ⟨a, p, hp⟩ := exists_epi_carrier_lowerStar_tensorObj_fourierKernel_inv ψ i q i' π hπ hw
    hP E fun h ↦ hD (D.isZero_of_isZero_carrier_directImage (h.of_iso c))
  exact ⟨a, D.hasLinearArtinSchreierConstituent_of_epi ψ (c.hom ≫ p)⟩

/-- **A punctual transform forces a linear geometric constituent** (blueprint
`proposition-fourier-transform-middle-extension--1`, Step 3). If the transform of the middle
extension `(j_*M)[1]` is a sheaf `G` of finite support in degree `0`, then by Fourier inversion
`(j_*M)[1](-1) ≅ FT_{ψ⁻¹}(G) ≅ (π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^* i^* G))[1]`, so `j_*M` and
`π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^* i^* G)` have the same underlying geometric sheaf. The latter surjects onto
some `ℒ_{ψ(a x)}` if `M ≠ 0`
(`AlgebraicGeometry.WeilSheaf.exists_epi_carrier_lowerStar_tensorObj_fourierKernel_inv`), and
restricting along `j` with `j^* j_* M = M` makes `ℒ_{ψ(a x)}|_U` a quotient of `M_k̄`. -/
theorem exists_hasLinearArtinSchreierConstituent_of_iso (hψ : ψ ≠ 1) (hD : ¬ IsZero D.sheaf)
    (G : WeilSheaf k₀ l (affineLine k₀)) (hG : (WeilSheaf.support G).Finite)
    (e : (fourierTransform ψ).obj D.middleExtension ≅ WeilSheaf.toComplex.obj G) :
    ∃ a : AlgebraicClosure k₀, D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j := by
  -- the dense open `V` off the support of `G`, and its reduced closed complement `Z`
  obtain ⟨V, hV, hVS⟩ := affineLine.exists_opens_dense_compl_finite _ hG
  have hz : IsZero ((WeilSheaf.upperStar V.ι).obj G) := by
    refine WeilSheaf.isZero_upperStar_of_forall_notMem_support V.ι G fun y hy ↦ ?_
    refine hVS _ hy ?_
    change V.ι.base y.1 ∈ (V : Set (affineLine k₀))
    rw [Scheme.Opens.ι_apply]
    exact y.1.2
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : TopologicalSpace.NoetherianSpace (affineLine k₀) := by
    have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    have : IsNoetherian (affineLine k₀) := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace V :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨Z, _, i, _, _, _, _, hi⟩ := exists_isReduced_isClosedImmersion_range_eq_compl V.ι
  let X' := pullback i (affinePlane.fst k₀)
  let q : X' ⟶ Z := pullback.fst i (affinePlane.fst k₀)
  let i' : X' ⟶ affinePlane k₀ := pullback.snd i (affinePlane.fst k₀)
  let : X'.Over (Spec (CommRingCat.of k₀)) := ⟨i' ≫ affinePlane k₀ ↘ Spec (CommRingCat.of k₀)⟩
  have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change q ≫ Z ↘ Spec (CommRingCat.of k₀) = i' ≫ affinePlane.fst k₀ ≫ _
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc, pullback.condition,
      Category.assoc]⟩
  let π : X' ⟶ affineLine k₀ := i' ≫ affinePlane.snd k₀
  have hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have := (IsPullback.of_hasPullback i (affinePlane.fst k₀)).paste_vert
      (IsPullback.of_hasPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    rwa [comp_over] at this
  have : IsFinite π := MorphismProperty.of_isPullback hP inferInstance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
  -- `FT_{ψ⁻¹}(G)` is the sheaf `π_*(i'^*𝓚_{ψ⁻¹} ⊗ q^* i^* G)` in degree `-1`
  obtain ⟨e₂⟩ := nonempty_iso_fourierTransform_toComplex_of_isPullback ψ⁻¹ V.ι i hi q i' π rfl
    (IsPullback.of_hasPullback i (affinePlane.fst k₀)) G hz
  exact D.exists_hasLinearArtinSchreierConstituent_of_iso_of_isPullback ψ hψ hD G e i q i' π rfl
    pullback.condition.symm hP _ e₂

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
