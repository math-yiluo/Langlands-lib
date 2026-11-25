/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual
public import WeilConjectures.WeilSheaf.FourierInversion.AffinePlaneAdd
public import WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity
public import WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisseQuotients

/-!
# The geometric linear characters are pairwise distinct

For `a ∈ k̄` let `ℒ_{ψ(a x)} = (a ·)^* ℒ_ψ` be the geometric linear Artin–Schreier sheaf on
`𝔸¹_{k̄}`. On the geometric fibre `Ū` of a dense open `U₀ ⊆ 𝔸¹`:

- `ℒ_{ψ(a x)}|_Ū` has rank one, hence is an irreducible local system
  (`AlgebraicGeometry.isIrreducibleAdicLocalSystem_upperStar_geometricSMul_artinSchreier`);
- for `a ≠ b` the restrictions `ℒ_{ψ(a x)}|_Ū` and `ℒ_{ψ(b x)}|_Ū` are not isomorphic
  (`WeilSheaf.LisseOnDenseOpen.isEmpty_iso_upperStar_geometricSMul_artinSchreier`):
  tensoring an isomorphism with `ℒ_{ψ(-b x)}` would make `ℒ_{ψ((a - b) x)}|_Ū` constant, but it is
  not even a quotient of a constant sheaf on the punctured disc at `∞`
  (`AlgebraicGeometry.affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage`).

The second statement uses the multiplicativity `ℒ_{ψ,f} ⊗ ℒ_{ψ,g} ≅ ℒ_{ψ,f+g}` of the
Artin–Schreier sheaves (blueprint `lemma-artin-schreier-character-sheaf`), proved here for the two
coordinates of the plane `𝔸²` after base change to `k̄`
(`AlgebraicGeometry.nonempty_iso_tensorLeft_upperStar_artinSchreier_add`) and pulled back along
`x ↦ (a x, b x)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀]

section Plane

omit [Finite k₀] in
lemma affineLine.geometricConst_add (a b : AlgebraicClosure k₀) :
    affineLine.geometricConst k₀ (a + b) =
      affineLine.geometricConst k₀ a + affineLine.geometricConst k₀ b := by
  simp [affineLine.geometricConst]

variable (k₀) in
/-- The geometric point `x ↦ (a x, b x)` of the plane over the geometric affine line, for
`a, b ∈ k̄`. -/
noncomputable def affinePlane.geometricPair (a b : AlgebraicClosure k₀) :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  pullback.lift (f := affinePlane k₀ ↘ Spec (CommRingCat.of k₀))
    (g := (Scheme.specAlgebraicClosure k₀).hom)
    (pullback.lift (f := affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (g := affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine.geometricSMul k₀ a ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (affineLine.geometricSMul k₀ b ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (by simp only [Category.assoc, Scheme.Hom.geometricFiber_condition,
        affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure_assoc]))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure (by
      change _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, Category.assoc, Scheme.Hom.geometricFiber_condition,
        affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure_assoc])

omit [Finite k₀] in
lemma affinePlane.geometricPair_comp_geometricFiberProj (a b : AlgebraicClosure k₀) :
    affinePlane.geometricPair k₀ a b ≫
        (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      pullback.lift
        (affineLine.geometricSMul k₀ a ≫
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
        (affineLine.geometricSMul k₀ b ≫
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
        (by simp only [Category.assoc, Scheme.Hom.geometricFiber_condition,
          affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure_assoc]) :=
  pullback.lift_fst _ _ _

omit [Finite k₀] in
lemma affinePlane.geometricPair_comp_geometricFiberToAlgebraicClosure (a b : AlgebraicClosure k₀) :
    affinePlane.geometricPair k₀ a b ≫
        (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
  pullback.lift_snd _ _ _

omit [Finite k₀] in
lemma affinePlane.geometricPair_comp_fst (a b : AlgebraicClosure k₀) :
    affinePlane.geometricPair k₀ a b ≫
        Scheme.Hom.geometricFiberMap (affinePlane.fst k₀) (comp_over _ _) =
      affineLine.geometricSMul k₀ a := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, affinePlane.geometricPair_comp_geometricFiberProj]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      affinePlane.geometricPair_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure]

omit [Finite k₀] in
lemma affinePlane.geometricPair_comp_snd (a b : AlgebraicClosure k₀) :
    affinePlane.geometricPair k₀ a b ≫
        Scheme.Hom.geometricFiberMap (affinePlane.snd k₀) (comp_over _ _) =
      affineLine.geometricSMul k₀ b := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, affinePlane.geometricPair_comp_geometricFiberProj]
    exact pullback.lift_snd _ _ _
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      affinePlane.geometricPair_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure]

omit [Finite k₀] in
lemma affinePlane.geometricPair_comp_add (a b : AlgebraicClosure k₀) :
    affinePlane.geometricPair k₀ a b ≫
        Scheme.Hom.geometricFiberMap (affinePlane.add k₀) (comp_over _ _) =
      affineLine.geometricSMul k₀ (a + b) := by
  have hfst : (affinePlane.geometricPair k₀ a b ≫
      (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) ≫ affinePlane.fst k₀ =
      affineLine.geometricSMul k₀ a ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := by
    rw [affinePlane.geometricPair_comp_geometricFiberProj]
    exact pullback.lift_fst _ _ _
  have hsnd : (affinePlane.geometricPair k₀ a b ≫
      (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) ≫ affinePlane.snd k₀ =
      affineLine.geometricSMul k₀ b ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := by
    rw [affinePlane.geometricPair_comp_geometricFiberProj]
    exact pullback.lift_snd _ _ _
  have key {T : Scheme.{u}} (P : T ⟶ affinePlane k₀) (g : affinePlane k₀ ⟶ affineLine k₀)
      (c : Γ(affineLine k₀, ⊤)) : (P ≫ g).appTop c = P.appTop (g.appTop c) := by
    rw [Scheme.Hom.comp_appTop P g]
    rfl
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← Category.assoc,
      affinePlane.add, AffineSpace.comp_homOfVector,
      affineLine.geometricSMul_comp_geometricFiberProj]
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_over]
      change _ ≫ pullback.fst _ _ ≫ _ = _
      rw [← Category.assoc]
      change (_ ≫ affinePlane.fst k₀) ≫ _ = _
      rw [hfst, Category.assoc, Scheme.Hom.geometricFiber_condition,
        affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure_assoc]
    · simp only [AffineSpace.homOfVector_appTop_coord, Function.comp_apply, map_add]
      rw [← key, ← key, hfst, hsnd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.geometricSMul_appTop_coord,
        affineLine.geometricSMul_appTop_coord, affineLine.geometricConst_add, add_mul]
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      affinePlane.geometricPair_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure]

end Plane

variable {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Multiplicativity of the Artin–Schreier sheaves** on the plane: for the two coordinate
functions `f = x` and `g = y` of `𝔸² = 𝔸¹ ×_{k₀} 𝔸¹`, `ℒ_{ψ,f} ⊗ ℒ_{ψ,g} ≅ ℒ_{ψ,f+g}`, where
`ℒ_{ψ,h} = h^* ℒ_ψ`; stated for the underlying sheaves on the geometric plane `𝔸²_{k̄}`, the tensor
product being that of sheaves of `ℚ̄_ℓ`-modules.
(blueprint: `lemma-artin-schreier-character-sheaf`, the clause `ℒ_{ψ,f} ⊗ ℒ_{ψ,g} ≅ ℒ_{ψ,f+g}` for
the coordinates `f = x`, `g = y` of `𝔸²`, after base change to `k̄`) -/
theorem nonempty_iso_tensorLeft_upperStar_artinSchreier_add (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((Mod.tensorLeft ((Scheme.Hom.geometricFiberMap (affinePlane.snd k₀)
          (comp_over _ _))^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)).obj
        ((Scheme.Hom.geometricFiberMap (affinePlane.fst k₀) (comp_over _ _))^*ᵃ[l].obj
          (artinSchreier ψ 1).obj.carrier) ≅
      (Scheme.Hom.geometricFiberMap (affinePlane.add k₀) (comp_over _ _))^*ᵃ[l].obj
        (artinSchreier ψ 1).obj.carrier) := by
  have hadd : affinePlane.add k₀ = affineLine.homOfSection k₀
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) +
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) := by
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [affinePlane.add, affineLine.homOfSection, AffineSpace.homOfVector_over]
    · rw [affinePlane.add, affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord]
  obtain ⟨e⟩ := nonempty_iso_ihom_upperStar_artinSchreier_of_eq (l := l) ψ _ _
    (affinePlane.fst k₀) (affinePlane.snd k₀) (affinePlane.add k₀)
    (affineLine.eq_homOfSection _) (affineLine.eq_homOfSection _) hadd
  obtain ⟨t⟩ := nonempty_tensorLeft_ihom_upperStar_artinSchreier (l := l) ψ
    (Scheme.Hom.geometricFiberMap (affinePlane.snd k₀) (comp_over _ _))
    ((Scheme.Hom.geometricFiberMap (affinePlane.add k₀) (comp_over _ _))^*ᵃ[l].obj
      (artinSchreier ψ 1).obj.carrier)
  exact ⟨(Mod.tensorLeft _).mapIso e ≪≫ t⟩

/-- **Multiplicativity of the geometric linear characters**:
`ℒ_{ψ(a x)} ⊗ ℒ_{ψ(b x)} ≅ ℒ_{ψ((a + b) x)}` on `𝔸¹_{k̄}`, for `a, b ∈ k̄`: the pullback of
`AlgebraicGeometry.nonempty_iso_tensorLeft_upperStar_artinSchreier_add` along `x ↦ (a x, b x)`,
pullback commuting with the tensor product. -/
theorem nonempty_iso_tensorLeft_upperStar_geometricSMul_artinSchreier
    (ψ : AddChar k₀ (PadicAlgCl l)) (a b : AlgebraicClosure k₀) :
    Nonempty ((Mod.tensorLeft ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj
          (artinSchreier ψ 1).obj.carrier)).obj
        ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) ≅
      (affineLine.geometricSMul k₀ (a + b))^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) := by
  obtain ⟨e⟩ := nonempty_iso_tensorLeft_upperStar_artinSchreier_add (l := l) ψ
  set L := (artinSchreier ψ 1).obj.carrier
  set γ := affinePlane.geometricPair k₀ a b
  let eF := ProEtale.adicUpperStarCompObjIso (affinePlane.geometricPair_comp_fst a b) L
  let eS := ProEtale.adicUpperStarCompObjIso (affinePlane.geometricPair_comp_snd a b) L
  let eA := ProEtale.adicUpperStarCompObjIso (affinePlane.geometricPair_comp_add a b) L
  exact ⟨(Mod.tensorLeftMapIso eS.symm).app _ ≪≫ (Mod.tensorLeft _).mapIso eF.symm ≪≫
    ((ProEtale.adicUpperStarTensorLeftIso l γ _).app _).symm ≪≫ (γ)^*ᵃ[l].mapIso e ≪≫ eA⟩

/-- The geometric linear character `ℒ_{ψ(a x)}` has rank one: its stalks are lines. By lissity
the rank is that of `ℒ_{ψ(0 · x)} ≅ ℚ̄_ℓ`. -/
theorem finrank_geometricStalkFunctor_upperStar_geometricSMul_artinSchreier
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) {Y : Scheme.{u}}
    (g : Y ⟶ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((ProEtale.geometricStalkFunctor l s).obj
        ((g)^*ᵃ[l].obj ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj
          (artinSchreier ψ 1).obj.carrier)))) = 1 := by
  obtain ⟨e₀⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l) ψ 1
  set L := (artinSchreier ψ 1).obj.carrier
  have hL : ProEtale.IsAdicLisseSheaf L := isLisse_artinSchreier ψ 1
  have h₁ := ProEtale.finrank_geometricStalkFunctor_upperStar g
    ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj L) s
  have h₂ := ProEtale.finrank_geometricStalkFunctor_upperStar (affineLine.geometricSMul k₀ a) L
    (s ≫ g)
  have h₃ := hL.finrank_geometricStalkFunctor_eq ((s ≫ g) ≫ affineLine.geometricSMul k₀ a)
    ((s ≫ g) ≫ affineLine.geometricSMul k₀ 0)
  have h₄ := ProEtale.finrank_geometricStalkFunctor_upperStar (affineLine.geometricSMul k₀ 0) L
    (s ≫ g)
  have h₅ : Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((ProEtale.geometricStalkFunctor l (s ≫ g)).obj
        ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj L))) =
      Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
        ((ProEtale.geometricStalkFunctor l (s ≫ g)).obj (ProEtale.AdicSheaf.unit l _))) :=
    ((ProEtale.geometricStalkFunctor l (s ≫ g) ⋙
      WeilCoefficients.toModuleCat l).mapIso e₀).toLinearEquiv.finrank_eq
  have h₆ := ProEtale.finrank_geometricStalkFunctor_unit (l := l) (s ≫ g)
  omega

/-- A geometric point of a nonempty scheme, at the algebraic closure of the residue field of some
point. -/
lemma exists_geometricPoint (Y : Scheme.{u}) [Nonempty Y] :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K), Nonempty (Spec (.of K) ⟶ Y) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y⟩⟩

namespace WeilSheaf.LisseOnDenseOpen

variable (D : LisseOnDenseOpen k₀ l) (ψ : AddChar k₀ (PadicAlgCl l))

/-- The restriction `ℒ_{ψ(a x)}|_Ū` of a geometric linear character to the geometric fibre of the
open `U₀`. -/
noncomputable abbrev linearCharacter (a : AlgebraicClosure k₀) :
    ProEtale.AdicSheaf l (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].obj
    ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)

/-- `ℒ_{ψ(a x)}|_Ū` is an irreducible local system: it is lisse of rank one on the irreducible
`Ū`. -/
theorem isIrreducibleAdicLocalSystem_linearCharacter (a : AlgebraicClosure k₀) :
    ProEtale.IsIrreducibleAdicLocalSystem (D.linearCharacter ψ a) := by
  have := D.irreducibleSpace_geometricFiber
  obtain ⟨K, _, _, ⟨s⟩⟩ := exists_geometricPoint (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  exact ProEtale.IsAdicLisseSheaf.isIrreducibleAdicLocalSystem_of_finrank_eq_one
    (ProEtale.IsAdicLisseSheaf.upperStar _
      (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1))) s
    (finrank_geometricStalkFunctor_upperStar_geometricSMul_artinSchreier ψ a _ s)

/-- `ℒ_{ψ(a x)}|_Ū ⊗ ℒ_{ψ(b x)}|_Ū ≅ ℒ_{ψ((a + b) x)}|_Ū`. -/
noncomputable def tensorLeftLinearCharacterIso (a b : AlgebraicClosure k₀) :
    (Mod.tensorLeft (D.linearCharacter ψ b)).obj (D.linearCharacter ψ a) ≅
      D.linearCharacter ψ (a + b) :=
  ((ProEtale.adicUpperStarTensorLeftIso l (Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))
      ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)).app
        ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)).symm ≪≫
    (Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].mapIso
      (nonempty_iso_tensorLeft_upperStar_geometricSMul_artinSchreier ψ a b).some

/-- **The geometric linear characters are pairwise distinct** on `Ū`: for `ψ ≠ 1` and `a ≠ b`
in `k̄`, `ℒ_{ψ(a x)}|_Ū ≇ ℒ_{ψ(b x)}|_Ū`. Tensoring with `ℒ_{ψ(-b x)}|_Ū`, an isomorphism would
give `ℒ_{ψ((a - b) x)}|_Ū ≅ ℒ_{ψ(0 · x)}|_Ū ≅ ℚ̄_ℓ`, while `ℒ_{ψ((a - b) x)}` is not a quotient of
a constant sheaf on the punctured disc at `∞`, through which `Ū` has a point. -/
theorem isEmpty_iso_linearCharacter (hψ : ψ ≠ 1) {a b : AlgebraicClosure k₀} (hab : a ≠ b) :
    IsEmpty (D.linearCharacter ψ a ≅ D.linearCharacter ψ b) := by
  refine ⟨fun e ↦ ?_⟩
  obtain ⟨e₀⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l) ψ 1
  set c := a + -b
  have hc : c ≠ 0 := by
    rw [show c = a - b from (sub_eq_add_neg a b).symm]
    exact sub_ne_zero.2 hab
  -- `ℒ_{ψ(c x)}|_Ū ≅ ℚ̄_ℓ`
  let E : D.linearCharacter ψ c ≅ ProEtale.AdicSheaf.unit l _ :=
    (D.tensorLeftLinearCharacterIso ψ a (-b)).symm ≪≫
      (Mod.tensorLeft (D.linearCharacter ψ (-b))).mapIso e ≪≫
      D.tensorLeftLinearCharacterIso ψ b (-b) ≪≫
      (Scheme.Hom.geometricFiberMap D.j (comp_over D.j _))^*ᵃ[l].mapIso
        ((ProEtale.adicUpperStarCongr l (congrArg (affineLine.geometricSMul k₀)
          (add_neg_cancel b))).app _ ≪≫ e₀) ≪≫
      ProEtale.adicUpperStarUnitIso l _
  have : Nonempty (affineLine k₀) :=
    ⟨(laurentPoint k₀ 1 ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (IsLocalRing.closedPoint (LaurentSeries (AlgebraicClosure k₀)))⟩
  have : Nonempty D.U := D.j.denseRange.nonempty
  obtain ⟨zU, hzU⟩ := exists_comp_geometricFiberMap_eq_laurentPoint k₀ D.j
  have hpt : (zU ≫ Scheme.Hom.geometricFiberMap D.j (comp_over D.j _) ≫
      affineLine.geometricSMul k₀ c) ≫
        Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1) (comp_over _ _) =
      laurentPoint k₀ (algebraMap k₀ (AlgebraicClosure k₀) 1 * (c * 1)) := by
    rw [Category.assoc, Category.assoc, reassoc_of% hzU,
      reassoc_of% laurentPoint_comp_geometricSMul, laurentPoint_comp_geometricFiberMap_smul]
  have hb : algebraMap k₀ (AlgebraicClosure k₀) 1 * (c * 1) ≠ 0 := by simpa using hc
  exact affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage ψ hψ hb (n := 1)
    (biproductUniqueIso (fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l _)).inv
    ((ProEtale.adicUpperStarUnitIso l zU).inv ≫ (zU)^*ᵃ[l].map E.inv ≫
      (zU)^*ᵃ[l].map (ProEtale.adicUpperStarCompObjIso rfl _).hom ≫
      (ProEtale.adicUpperStarCompObjIso rfl _).hom ≫
      (ProEtale.adicUpperStarCompObjIso hpt _).hom ≫
      (laurentPoint k₀ _)^*ᵃ[l].map (affineLine.artinSchreierCarrierIso ψ).hom)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
