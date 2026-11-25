/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraBasic
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Additive affine sections of the coproduct of conormal pieces

Source: Stacks Project, Divisors, Lemma 0633, part (2).
(blueprint: lem-pur-conormal-coproduct-affine-add-equiv).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
namespace AlgebraicGeometry.ConormalGradedAlgebra

private theorem power_qc {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (Scheme.idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  · exact (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.1 n hn

private theorem power_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (V : X.affineOpens) (n : ℕ) :
    Set.range ((Scheme.idealSheafPower I.toModulesι n).2.app V.1) =
      {a | a ∈ I.ideal V ^ n} := by
  cases n with
  | zero =>
    simp only [Scheme.idealSheafPower, Scheme.Modules.Hom.id_app, pow_zero]
    ext a
    simp
  | succ n =>
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 V).2.2.2 (n + 1) (Nat.succ_pos n)

private theorem projection_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (V : X.affineOpens) :
    Function.Surjective ((formalAssociatedGradedπ I n).app V.1) := by
  have := power_qc I n
  exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (Scheme.idealSheafPower I.toModulesι n).1).2.2.2.1 V).2.1

private theorem projection_kernel {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (V : X.affineOpens)
    (a : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)) :
    (formalAssociatedGradedπ I n).app V.1 a = 0 ↔
      (@id Γ(X, V.1) ((Scheme.idealSheafPower I.toModulesι n).2.app V.1 a)) ∈
        I.ideal V ^ (n + 1) := by
  have := power_qc I n
  have hker := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (Scheme.idealSheafPower I.toModulesι n).1).2.2.2.1 V).2.2.1 a
  change (formalAssociatedGradedπ I n).app V.1 a = 0 ↔
    a ∈ I.ideal V • (⊤ : Submodule Γ(X, V.1)
      Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)) at hker
  rw [hker]
  let im : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) :=
    ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1)).hom
  have hr : (LinearMap.range im : Ideal Γ(X, V.1)) = I.ideal V ^ n := by
    apply SetLike.coe_injective
    exact power_range I V n
  have hmap : Submodule.map im (I.ideal V • ⊤) = I.ideal V ^ (n + 1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hr, Ideal.smul_eq_mul, pow_succ']
  constructor
  · intro ha
    rw [← hmap]
    exact Submodule.mem_map_of_mem ha
  · intro ha
    rw [← hmap] at ha
    obtain ⟨b, hb, hba⟩ := ha
    exact formalPolynomial_power_injective I.toModulesι n V.1 hba ▸ hb

private theorem formal_piece_equiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (V : X.affineOpens) :
    ∃ e : Γ(formalAssociatedGradedPiece I n, V.1) ≃ₗ[Γ(X, V.1)]
        Ideal.associatedGradedPiece (I.ideal V) n,
      ∀ a : Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1),
        ∃ h : (Scheme.idealSheafPower I.toModulesι n).2.app V.1 a ∈ I.ideal V ^ n,
          e ((formalAssociatedGradedπ I n).app V.1 a) =
            Submodule.Quotient.mk ⟨(Scheme.idealSheafPower I.toModulesι n).2.app V.1 a, h⟩ := by
  let R := Γ(X, V.1)
  let P := Γ((Scheme.idealSheafPower I.toModulesι n).1, V.1)
  let inc : P →ₗ[R] R := ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1)).hom
  have hi (a : P) : inc a ∈ I.ideal V ^ n := by
    change inc a ∈ {a | a ∈ I.ideal V ^ n}
    rw [← power_range I V n]
    exact ⟨a, rfl⟩
  let inc' : P →ₗ[R] (I.ideal V ^ n : Ideal R) := inc.codRestrict _ hi
  let f : P →ₗ[R] Ideal.associatedGradedPiece (I.ideal V) n :=
    (Submodule.comap (I.ideal V ^ n).subtype (I.ideal V ^ (n + 1))).mkQ.comp inc'
  let q := ((formalAssociatedGradedπ I n).val.app (op V.1)).hom
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    have har : (a : R) ∈ Set.range ((Scheme.idealSheafPower I.toModulesι n).2.app V.1) := by
      rw [power_range I V n]
      exact a.property
    obtain ⟨b, hb⟩ := har
    refine ⟨b, ?_⟩
    change Submodule.Quotient.mk (inc' b) = Submodule.Quotient.mk a
    congr 1
    exact Subtype.ext hb
  have hk : LinearMap.ker q = LinearMap.ker f := by
    ext a
    change q a = 0 ↔ f a = 0
    have hf0 : f a = 0 ↔ inc a ∈ I.ideal V ^ (n + 1) :=
      Submodule.Quotient.mk_eq_zero
        (Submodule.comap (I.ideal V ^ n).subtype (I.ideal V ^ (n + 1)))
    exact (projection_kernel I n V a).trans hf0.symm
  let e := (q.quotKerEquivOfSurjective (projection_surjective I n V)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hk ≪≫ₗ f.quotKerEquivOfSurjective hf
  refine ⟨e, fun a ↦ ⟨hi a, ?_⟩⟩
  change f.quotKerEquivOfSurjective hf
    (Submodule.quotEquivOfEq _ _ hk
      ((q.quotKerEquivOfSurjective (projection_surjective I n V)).symm (q a))) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

-- Lift the cofan into quasi-coherent modules, then apply the inverse tilde equivalence.
-- The ULift allows the existing coproduct-closure theorem to handle a small index type.
private noncomputable def spec_coproduct {R : CommRingCat.{u}} {ι : Type}
    (F : ι → (Spec R).Modules) [∀ n, (F n).IsQuasicoherent]
    (M : (Spec R).Modules) (j : ∀ n, F n ⟶ M) (hc : IsColimit (Cofan.mk M j)) :
    IsColimit (Cofan.mk ((moduleSpecΓFunctor (R := R)).obj M)
      (fun n ↦ (moduleSpecΓFunctor (R := R)).map (j n))) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (Sigma.reindex (Equiv.ulift : ULift.{u} ι ≃ ι) F ≪≫
        (coproductIsCoproduct F).coconePointUniqueUpToIso hc)
      (Scheme.Modules.isQuasicoherent_sigma (fun n : ULift.{u} ι ↦ F n.down))
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F' : ι → Q.FullSubcategory := fun n ↦ ⟨F n, inferInstance⟩
  let M' : Q.FullSubcategory := ⟨M, inferInstance⟩
  let j' : ∀ n, F' n ⟶ M' := fun n ↦ ObjectProperty.homMk (j n)
  have hc' : IsColimit (Cofan.mk M' j') :=
    isColimitOfIsColimitCofanMkObj Q.ι F' j' hc
  exact isColimitCofanMkObjOfIsColimit
    (tildeEquiv (R := R)).inverse F' j' hc'

-- Restrict to the canonical affine chart and transport its global sections back to V.
private theorem affine_coproduct_equiv {Y : Scheme.{u}} {ι : Type} [DecidableEq ι]
    (F : ι → Y.Modules) [∀ n, (F n).IsQuasicoherent]
    (M : Y.Modules) (j : ∀ n, F n ⟶ M) (hc : IsColimit (Cofan.mk M j))
    (V : Y.affineOpens) :
    ∃ e : Γ(M, V.1) ≃+ ⨁ n, Γ(F n, V.1),
      ∀ n (a : Γ(F n, V.1)), e ((j n).app V.1 a) = DirectSum.of _ n a := by
  classical
  let T := Scheme.Modules.restrictFunctor V.2.fromSpec
  let G := moduleSpecΓFunctor (R := Γ(Y, V.1))
  have hT := isColimitCofanMkObjOfIsColimit T F j hc
  have hG := spec_coproduct (fun n ↦ T.obj (F n)) (T.obj M) (fun n ↦ T.map (j n)) hT
  let s := hG.coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit (fun n ↦ G.obj (T.obj (F n))))
  have hs (n : ι) (a : G.obj (T.obj (F n))) :
      s.hom (G.map (T.map (j n)) a) = DirectSum.of _ n a := by
    exact ConcreteCategory.congr_hom
      (hG.comp_coconePointUniqueUpToIso_hom
        (ModuleCat.coproductCoconeIsColimit (fun n ↦ G.obj (T.obj (F n))))
        (Discrete.mk n)) a
  have hV : V.2.fromSpec ''ᵁ ⊤ = V.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, V.2.opensRange_fromSpec]
  let e (N : Y.Modules) : G.obj (T.obj N) ≃+ Γ(N, V.1) :=
    ((N.restrictAppIso V.2.fromSpec ⊤) ≪≫
      N.presheaf.mapIso (eqToIso (congrArg op hV))).addCommGroupIsoToAddEquiv
  have he {N P : Y.Modules} (f : N ⟶ P) (a : G.obj (T.obj N)) :
      e P (G.map (T.map f) a) = f.app V.1 (e N a) := by
    exact (PresheafOfModules.naturality_apply f.val (eqToHom (congrArg op hV)) a).symm
  refine ⟨(e M).symm.trans
    (s.toLinearEquiv.toAddEquiv.trans (DirectSum.congrAddEquiv fun n ↦ e (F n))), ?_⟩
  intro n a
  have hn := he (j n) ((e (F n)).symm a)
  rw [AddEquiv.apply_symm_apply] at hn
  change DirectSum.congrAddEquiv (fun n ↦ e (F n))
    (s.hom ((e M).symm ((j n).app V.1 a))) = _
  rw [← hn, AddEquiv.symm_apply_apply, hs]
  change DirectSum.map (fun n ↦ (e (F n)).toAddMonoidHom)
    (DirectSum.of _ n ((e (F n)).symm a)) = _
  rw [DirectSum.map_of]
  exact congrArg (DirectSum.of _ n) ((e (F n)).apply_symm_apply a)

-- The normalized closed-immersion quotient comparison uses the same chosen adjunction
-- as representative, so the projection equation supplies the normalization directly.
private theorem piece_equiv {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (U : X.affineOpens) :
    ∃ e : Γ(piece i n, i ⁻¹ᵁ U.1) ≃+
        Ideal.associatedGradedPiece (i.ker.ideal U) n,
      ∀ a : Γ(power i n, U.1),
        ∃ h : (powerInclusion i n).app U.1 a ∈ i.ker.ideal U ^ n,
          e (representative i n U.1 a) =
            Submodule.Quotient.mk ⟨(powerInclusion i n).app U.1 a, h⟩ := by
  classical
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)
  obtain ⟨b, hb⟩ := closedImmersion_power_quotient i.ker 1 i (by simp) adj (power i n)
  let b' : formalAssociatedGradedPiece i.ker n ≅
      (Scheme.Modules.pushforward i).obj (piece i n) := b
  let eb := ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).mapIso b').toLinearEquiv
  obtain ⟨e, he⟩ := formal_piece_equiv i.ker n U
  refine ⟨eb.toAddEquiv.symm.trans e.toAddEquiv, ?_⟩
  intro a
  obtain ⟨h, ha⟩ := he a
  refine ⟨h, ?_⟩
  have hrep := congrArg (fun f ↦ f.val.app (op U.1) a) hb
  change eb ((formalAssociatedGradedπ i.ker n).app U.1 a) = representative i n U.1 a at hrep
  change e (eb.symm (representative i n U.1 a)) = _
  rw [← hrep, LinearEquiv.symm_apply_apply]
  exact ha

/-- Affine sections of a module coproduct of conormal pieces are the additive
sum of the ideal-power quotients. No ring structure on the coproduct is assumed.
Source: Stacks Project, Divisors, Lemma 0633, part (2).
(blueprint: lem-pur-conormal-coproduct-affine-add-equiv).

Proof: The power inclusion identifies the affine sections of `I^n` with `J^n`.
The affine quotient projection is surjective with kernel `J` times these sections,
which the inclusion identifies with `J^(n+1)`. The normalized closed-immersion
quotient isomorphism identifies this quotient sheaf with `i_* i^* I^n` and its
projection with the specified adjunction unit. Thus it gives the degreewise
quotient equivalence, sending the adjunction-unit representative to its class.
These pieces are quasi-coherent. On the affine inverse
image of the ambient affine open, the tilde/global-sections equivalence identifies
their sheaf coproduct with the tilde of their module direct sum; restriction to
this open preserves coproducts. Taking sections and composing the degreewise
quotient identifications gives the additive equivalence and its normalization.
The proof uses neither multiplication on the coproduct nor its unit, and applies
also to `n = 0`, the unit ideal, the zero ideal and the empty inverse image. -/
theorem exists_conormalCoproduct_affine_addEquiv {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (j : ∀ n, piece i n ⟶ M)
    (hc : IsColimit (Cofan.mk M j)) (U : X.affineOpens) :
    ∃ e : M.val.obj (op (i ⁻¹ᵁ U.1)) ≃+ Ideal.associatedGraded (i.ker.ideal U),
      ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
        ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
          e ((j n).val.app (op (i ⁻¹ᵁ U.1)) (representative i n U.1 a)) =
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩) := by
  classical
  have (n : ℕ) : (power i n).IsQuasicoherent := power_qc i.ker n
  have (n : ℕ) : (piece i n).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorPullback i (power i n)
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  obtain ⟨s, hs⟩ := affine_coproduct_equiv (piece i) M j hc V
  choose e he using fun n ↦ piece_equiv i n U
  refine ⟨s.trans (DirectSum.congrAddEquiv e), ?_⟩
  intro n a
  obtain ⟨h, ha⟩ := he n a
  refine ⟨h, ?_⟩
  change DirectSum.congrAddEquiv e (s ((j n).app V.1 (representative i n U.1 a))) = _
  rw [hs]
  change DirectSum.map (fun n ↦ (e n).toAddMonoidHom)
    (DirectSum.of _ n (representative i n U.1 a)) = _
  rw [DirectSum.map_of]
  exact congrArg (DirectSum.of _ n) ha

end AlgebraicGeometry.ConormalGradedAlgebra
