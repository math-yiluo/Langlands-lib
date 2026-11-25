/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sp.SpEllCoefficientTower

/-! # The normalized basis at one finite Tate level

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), finite bases.
(blueprint: lem-sp-root-basis-level)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.ProEtale

private def cyclicTensorInsertion {N : ℕ} {A : Type (u + 1)} [AddCommGroup A] :
    A →ₗ[ℤ] A ⊗[ℤ] ULift.{u + 1} (ZMod N) :=
  (TensorProduct.mk ℤ A (ULift.{u + 1} (ZMod N))).flip 1

private theorem cyclicTensorInsertion_bijective {N : ℕ} {A : Type (u + 1)}
    [AddCommGroup A] (hA : ∀ a : A, N • a = 0) :
    Function.Bijective (cyclicTensorInsertion.{u} (N := N) (A := A)) := by
  let : Module (ZMod N) A := AddCommGroup.zmodModule hA
  let f : A →+ ULift.{u + 1} (ZMod N) →+ A :=
    { toFun := fun b ↦
        { toFun := fun a ↦ a.down • b
          map_zero' := zero_smul _ b
          map_add' := fun a c ↦ add_smul a.down c.down b }
      map_zero' := by ext a; exact smul_zero a.down
      map_add' := fun b c ↦ by ext a; exact smul_add a.down b c }
  let q : A ⊗[ℤ] ULift.{u + 1} (ZMod N) →+ A :=
    TensorProduct.liftAddHom f (by
      intro z b a
      change a.down • (z • b) = (z • a.down) • b
      rw [smul_comm, smul_assoc])
  have hq (b : A) : q (cyclicTensorInsertion.{u} (N := N) b) = b := by
    change (1 : ZMod N) • b = b
    exact one_smul _ b
  have hp (z : A ⊗[ℤ] ULift.{u + 1} (ZMod N)) :
      cyclicTensorInsertion.{u} (N := N) (q z) = z := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b a =>
      obtain ⟨a⟩ := a
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
      change ((k : ZMod N) • b) ⊗ₜ[ℤ] (1 : ULift.{u + 1} (ZMod N)) =
        b ⊗ₜ[ℤ] ULift.up (k : ZMod N)
      rw [Int.cast_smul_eq_zsmul, TensorProduct.smul_tmul]
      congr 1
      apply ULift.ext
      change k • (1 : ZMod N) = (k : ZMod N)
      simp only [zsmul_eq_mul, mul_one]
  constructor
  · intro b c h
    exact (hq b).symm.trans ((congrArg q h).trans (hq c))
  · intro z
    exact ⟨q z, hp z⟩

private theorem tensorComparison_mem (X : Scheme.{u})
    (B M : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (Scheme.ProEt.topology X).W
      (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
        AddCommGrpCat.{u + 1}) B M) := by
  let J := Scheme.ProEt.topology X
  let adj := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let φ := Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{u + 1}) B.obj M.obj ≫
    (adj.counit.app B ⊗ₘ adj.counit.app M)
  have : IsIso φ := by dsimp [φ]; infer_instance
  change J.W (adj.homEquiv _ _ φ)
  rw [Adjunction.homEquiv_unit]
  exact J.W.comp_mem _ _ (J.W_adj_unit_app adj _) (J.W.of_isIso _)

private theorem freeTensor_pair_smul (X : Scheme.{u})
    (R B : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj B]
    (q : R ⟶ B) [IsMonHom q]
    (M : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (U : X.ProEtᵒᵖ)
    (r : (InternalAbelianSheafModule.sectionRingSheaf
      (Scheme.ProEt.topology X) R).obj.obj U)
    (b : ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) R).obj ((Mod.comap q).obj (Mod.regular B))).val.obj U)
    (m : M.obj.obj U) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
      AddCommGrpCat.{u + 1}) B M).app U ((r • b) ⊗ₜ[ℤ] m) =
    r • (show ((InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) R).obj
        ((Mod.comap q).obj ((Mod.free B).obj M))).val.obj U from
      (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
        AddCommGrpCat.{u + 1}) B M).app U (b ⊗ₜ[ℤ] m)) := by
  let F := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
  have h :
      (F.obj R ◁ Functor.LaxMonoidal.μ F B M) ≫
        Functor.LaxMonoidal.μ F R (B ⊗ M) ≫
        F.map ((q ▷ (B ⊗ M)) ≫ (α_ B B M).inv ≫ MonObj.mul ▷ M) =
      (α_ (F.obj R) (F.obj B) (F.obj M)).inv ≫
        ((Functor.LaxMonoidal.μ F R B ≫ F.map (q ▷ B ≫ MonObj.mul)) ▷ F.obj M) ≫
          Functor.LaxMonoidal.μ F B M := by
    rw [associator_inv_naturality_left_assoc]
    simp only [Functor.map_comp]
    rw [Functor.LaxMonoidal.associativity_inv_assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc F (q ▷ B) M]
    rw [← Functor.LaxMonoidal.μ_natural_left F
      (show B ⊗ B ⟶ B from MonObj.mul) M]
    simp only [comp_whiskerRight, Category.assoc]
  have he := congrArg (fun t ↦ (t.app U) (r ⊗ₜ[ℤ] (b ⊗ₜ[ℤ] m))) h
  exact he.symm

private def rootTensorInsertion (X : Scheme.{u})
    (R B : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj B]
    (q : R ⟶ B) [IsMonHom q] (W : X.ProEt)
    (M : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (ζ : M.obj.obj (op W)) :
    ((InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology X) R).obj
      ((Mod.comap q).obj (Mod.regular B))).over W ⟶
    ((InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology X) R).obj
      ((Mod.comap q).obj ((Mod.free B).obj M))).over W := by
  let tensorMap := Functor.LaxMonoidal.μ
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) B M
  let p : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := (Over.forget W).op ⋙ B.obj
  let t : p ⟶ (Over.forget W).op ⋙ (B ⊗ M).obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        ((tensorMap.app (op V.unop.left)).hom.comp
          ((TensorProduct.mk ℤ (B.obj.obj (op V.unop.left))
            (M.obj.obj (op V.unop.left))).flip
              (M.obj.map V.unop.hom.op ζ)).toAddMonoidHom)
      naturality := by
        intro V V' f
        ext b
        have hζ : M.obj.map f.unop.left.op (M.obj.map V.unop.hom.op ζ) =
            M.obj.map V'.unop.hom.op ζ := by
          change (M.obj.map V.unop.hom.op ≫ M.obj.map f.unop.left.op) ζ = _
          rw [← Functor.map_comp, ← op_comp, Over.w f.unop]
        have h := NatTrans.naturality_apply tensorMap f.unop.left.op
          (b ⊗ₜ[ℤ] M.obj.map V.unop.hom.op ζ)
        change tensorMap.app (op V'.unop.left)
            (B.obj.map f.unop.left.op b ⊗ₜ[ℤ]
              M.obj.map f.unop.left.op (M.obj.map V.unop.hom.op ζ)) = _ at h
        change tensorMap.app (op V'.unop.left)
            (B.obj.map f.unop.left.op b ⊗ₜ[ℤ] M.obj.map V'.unop.hom.op ζ) = _
        rw [hζ] at h
        exact h }
  exact ⟨PresheafOfModules.homMk t (by
    intro V r b
    exact freeTensor_pair_smul X R B q M (op V.unop.left) r b
      (M.obj.map V.unop.hom.op ζ))⟩

private theorem spCoefficient_nsmul (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) (U : X.ProEtᵒᵖ)
    (b : (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X).obj.obj U) :
    (ℓ ^ (n + 1)) • b = 0 := by
  let B := spEllQuotient ℓ E n
  have hB : (ℓ ^ (n + 1) : B) = 0 := by
    have h : (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) (ℓ ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_pow, map_natCast] using h
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := DiscreteTopology.topologicalRing
  have h : (ℓ ^ (n + 1)) • 𝟙 (spEllPointRingObj.{u} ℓ E n) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (ℓ ^ (n + 1)) • _ = (0 : B)
    rw [nsmul_eq_mul, Nat.cast_pow, hB, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have : CategoryTheory.Limits.PreservesBinaryBiproducts (upperStarFromPoint X) :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hX : (ℓ ^ (n + 1)) • 𝟙 ((upperStarFromPoint X).obj
      (spEllPointRingObj.{u} ℓ E n)) = 0 := by
    calc
      _ = (upperStarFromPoint X).map ((ℓ ^ (n + 1)) •
          𝟙 (spEllPointRingObj.{u} ℓ E n)) := by
        rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      _ = 0 := by rw [h, Functor.map_zero]
  exact congrArg (fun t ↦ t.hom.app U b) hX

/-- A prescribed root basis gives the normalized linear basis of one finite
integral twist level on its slice.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), the map
`a ↦ zeta_n tensor a` at a fixed finite level.
(blueprint: lem-sp-root-basis-level)

Proof: write N = ell^(n+1) and B = O_E/(N). The canonical finite-discrete
coefficient comparison identifies the actual coefficient sheaf with constant B,
including its ring operations. On the slice, tensor the given root basis with B.
The integer tensor and the tensor over the constant Z/N sheaf coincide: locally
lift a residue scalar to an integer, for which balancing is ordinary integer
balancing; separatedness descends that equality. Restriction commutes with the
sheafification of these tensors because slice coverings are the original
coverings of each object. The resulting inverse sends b tensor z to b times
the image in B of e inverse of z. The balancing equations make this well defined.
The two composites are identities on pure tensors and hence after sheafification.
Both maps retain the B action, and therefore the O_E action through reduction.
The forward map sends every section b to b tensor the restricted zeta, by the
normalization of e. The same argument includes the zero coefficient ring and
empty slices. This assertion involves one level and no transition maps. -/
theorem spRootBasisLevel
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (W : X.ProEt) (n : ℕ)
    (ζ : (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e :
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (he : ∀ (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      e.hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op ζ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ i : (spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W).obj
          (spEllCoefficientLevel X ℓ E n) ≅
      (spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W).obj
          (spIntegralTwistLevel X ℓ E n),
      ∀ (V : (Over W)ᵒᵖ)
        (b : ((spRootBasisSliceSections X
          (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W).obj
            (spEllCoefficientLevel X ℓ E n)).val.obj V),
        i.hom.val.app V b =
          (Functor.LaxMonoidal.μ
            (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
            (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)
            (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))).app (op V.unop.left)
              (b ⊗ₜ[ℤ] (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op ζ) := by
  let J := Scheme.ProEt.topology X
  let F := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let B := condensedRingObj.{u} (spEllPointRingObj ℓ E n) X
  let M := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
  let K := Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)
  let S := spRootBasisSliceSections X R W
  let A := S.obj (spEllCoefficientLevel X ℓ E n)
  let T := S.obj (spIntegralTwistLevel X ℓ E n)
  let p : A ⟶ T := rootTensorInsertion X R B (spEllReduction X ℓ E n) W M ζ
  let H := (Over.forget W).op
  let B' := H ⋙ B.obj
  let Z := (Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
  let κ := Functor.whiskerRight (toSheafify J Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  have hκi : Presheaf.IsLocallyInjective J κ := by
    apply (Presheaf.isLocallyInjective_forget_iff J κ).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J Z) (forget CommRingCat.{u + 1}))
    infer_instance
  have hκs : Presheaf.IsLocallySurjective J κ := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J κ).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J Z) (forget CommRingCat.{u + 1}))
    infer_instance
  have hκ : J.W κ := J.W_of_isLocallyBijective κ
  let j := Functor.whiskerLeft H (B.obj ◁ κ)
  have hji : Presheaf.IsLocallyInjective (J.over W) j := by
    have := (hκ.whiskerLeft B.obj).isLocallyInjective
    exact Presheaf.isLocallyInjective_whisker (J.over W) J (Over.forget W) _
  have hjs : Presheaf.IsLocallySurjective (J.over W) j := by
    have := (hκ.whiskerLeft B.obj).isLocallySurjective
    exact Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W) _
  let v := (PresheafOfModules.toPresheaf (K.over W).obj).map e.hom.val
  let k := B' ◁ v
  have hk : IsIso k := by
    have : IsIso e.hom.val := by
      change IsIso ((SheafOfModules.forget (K.over W)).map e.hom)
      infer_instance
    dsimp only [k, v]
    infer_instance
  let tensorMap := Functor.whiskerLeft H (Functor.LaxMonoidal.μ F B M)
  have hμi : Presheaf.IsLocallyInjective (J.over W) tensorMap := by
    have := (tensorComparison_mem X B M).isLocallyInjective
    exact Presheaf.isLocallyInjective_whisker (J.over W) J (Over.forget W) _
  have hμs : Presheaf.IsLocallySurjective (J.over W) tensorMap := by
    have := (tensorComparison_mem X B M).isLocallySurjective
    exact Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W) _
  let a : B' ⟶ H ⋙ (B.obj ⊗ (Z ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    { app := fun V ↦ AddCommGrpCat.ofHom (cyclicTensorInsertion.toAddMonoidHom)
      naturality := by
        intro V V' f
        ext b
        rfl }
  have hai : Presheaf.IsLocallyInjective (J.over W) a := by
    apply Presheaf.isLocallyInjective_of_injective
    intro V
    exact (cyclicTensorInsertion_bijective
      (spCoefficient_nsmul X ℓ E n (op V.unop.left))).1
  have has : Presheaf.IsLocallySurjective (J.over W) a := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro V
    exact (cyclicTensorInsertion_bijective
      (spCoefficient_nsmul X ℓ E n (op V.unop.left))).2
  have hp : ((SheafOfModules.toSheaf _).map p).hom = a ≫ j ≫ k ≫ tensorMap := by
    ext V b
    have h1 : κ.app (op V.unop.left) (1 : ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))) =
        (1 : K.obj.obj (op V.unop.left)) := by
      exact ((toSheafify J Z).app (op V.unop.left)).hom.map_one
    change (Functor.LaxMonoidal.μ F B M).app (op V.unop.left)
        (b ⊗ₜ[ℤ] M.obj.map V.unop.hom.op ζ) =
      (Functor.LaxMonoidal.μ F B M).app (op V.unop.left)
        (b ⊗ₜ[ℤ] e.hom.val.app V
          (κ.app (op V.unop.left) (1 : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))))
    rw [h1, he, one_smul]
    rfl
  have hpi : Presheaf.IsLocallyInjective (J.over W)
      ((SheafOfModules.toSheaf _).map p).hom := by
    rw [hp]
    infer_instance
  have hps : Presheaf.IsLocallySurjective (J.over W)
      ((SheafOfModules.toSheaf _).map p).hom := by
    rw [hp]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map p) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨(Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hpi,
      (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hps⟩
  have : IsIso p := isIso_of_reflects_iso p (SheafOfModules.toSheaf _)
  exact ⟨asIso p, fun _ _ ↦ rfl⟩

end AlgebraicGeometry.ProEtale
