/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction

/-! # Residue factorization of evaluated simultaneous derived reduction

Source: diagonal tower system proof, step (2), and evaluation in step (4).
(blueprint: lem-sfb-diagonal-residue-derived-factorization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u wB wC
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The residue projection is onto by natural representatives. -/
theorem diagonalResidueProjection_surjective (ℓ n : ℕ) [Fact ℓ.Prime] :
    Function.Surjective (diagonalResidueProjection.{u} ℓ n) := by
  intro x
  refine ⟨ULift.up (x.down.val : ℤ_[ℓ]), ?_⟩
  apply ULift.ext
  change PadicInt.toZModPow (n + 1) (x.down.val : ℤ_[ℓ]) = x.down
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- The kernel of the residue projection Z_ℓ → Z/ℓ^(n+1) is (ℓ^(n+1)). -/
theorem diagonalResidueProjection_ker (ℓ n : ℕ) [Fact ℓ.Prime] :
    RingHom.ker (diagonalResidueProjection.{u} ℓ n) =
      Ideal.span {((ℓ ^ (n + 1) : ℕ) : ULift.{u + 1} ℤ_[ℓ])} := by
  ext x
  have hx : diagonalResidueProjection.{u} ℓ n x = 0 ↔
      PadicInt.toZModPow (n + 1) x.down = 0 := by
    constructor
    · intro h
      exact congrArg ULift.down h
    · intro h
      exact ULift.ext h
  rw [RingHom.mem_ker, hx, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨ULift.up z, ULift.ext (by simpa using hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.down, by simpa using congrArg ULift.down hz⟩

private theorem ordinary_residue_factorization (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (O : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ W)) :
    ∃ (E : DiagonalAb W ⥤
        Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
      (_ : E.Additive),
      Nonempty (E ⋙ diagonalFiniteToPadic ℓ n W ≅
        O.E ⋙ (evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)) := by
  let J := Scheme.ProEt.topology W
  let L := diagonalScalarExtension ℓ W
  let : L.Additive := scalarExtension_additive ℓ W
  let q := diagonalResidueProjection.{u} ℓ n
  let a : ULift.{u + 1} ℤ_[ℓ] := (ℓ ^ (n + 1) : ℕ)
  let rd := Sheaf.reductionDatum J q (diagonalResidueProjection_surjective ℓ n) a
    (diagonalResidueProjection_ker ℓ n)
  let E := L ⋙ rd.Φ
  have hσ (M : DiagonalMod ℓ W) :
      (Sheaf.smulNatTrans J a).app M = ℓ ^ (n + 1) • 𝟙 M := by
    change ((ℓ ^ (n + 1) : ℕ) : ULift.{u + 1} ℤ_[ℓ]) • 𝟙 M = _
    simp only [Nat.cast_smul_eq_nsmul]
  have hz (M : DiagonalAb W) :
      (ℓ ^ (n + 1) • 𝟙 (L.obj M)) ≫ rd.r.app (L.obj M) = 0 := by
    rw [← hσ]
    exact rd.σ_comp_r _
  have hc (M : DiagonalAb W) :
      IsColimit (CokernelCofork.ofπ (rd.r.app (L.obj M)) (hz M)) := by
    let := rd.epi_r (L.obj M)
    have h := (rd.exact (L.obj M)).gIsCokernel
    exact CokernelCofork.isColimitOfIsColimitOfIff' h
      (ℓ ^ (n + 1) • 𝟙 (L.obj M)) (by
        intro Z φ
        change L.obj M ⟶ Z at φ
        exact Iff.of_eq (congrArg (fun g : L.obj M ⟶ L.obj M ↦ g ≫ φ = 0)
          (hσ (L.obj M))))
  let c (M : DiagonalAb W) := (hc M).coconePointUniqueUpToIso (O.quotient n M)
  have hfac (M : DiagonalAb W) : rd.r.app (L.obj M) ≫ (c M).hom = (O.π n).app M :=
    (hc M).comp_coconePointUniqueUpToIso_hom (O.quotient n M) WalkingParallelPair.one
  refine ⟨E, inferInstance, ⟨NatIso.ofComponents c ?_⟩⟩
  intro M N f
  let := rd.epi_r (L.obj M)
  apply (cancel_epi (rd.r.app (L.obj M))).1
  change rd.r.app (L.obj M) ≫
    (rd.Φ ⋙ Sheaf.restrictScalars J q).map (L.map f) ≫ (c N).hom = _
  rw [← rd.r.naturality_assoc, hfac, ← Category.assoc, hfac]
  exact (O.π n).naturality f

@[irreducible] private def mapped_counit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    DerivedCategory.Q ⋙ (T ⋙ F.mapDerivedCategory) ⟶
      (E ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε F.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategoryFactors.hom

private theorem mapped_counit_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (E : A ⥤ B) [E.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) [IsIso (ε.app P)] :
    IsIso ((mapped_counit E T ε F).app P) := by
  simp only [mapped_counit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp]
  infer_instance

private theorem common_resolution_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (hε : ∀ P, good P → IsIso (ε.app P))
    (G : DerivedCategory A ⥤ DerivedCategory B)
    (β : DerivedCategory.Q ⋙ G ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hβ : ∀ P, good P → IsIso (β.app P)) : Nonempty (G ≅ T) := by
  let τ := T.leftDerivedLift ε (HomologicalComplex.quasiIso A (.up ℤ)) G β
  have hi (P : CochainComplex A ℤ) (hP : good P) :
      IsIso (τ.app (DerivedCategory.Q.obj P)) := by
    let := hε P hP
    have h := T.leftDerived_fac_app ε (HomologicalComplex.quasiIso A (.up ℤ)) G β P
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ ε.app P) := by
      rw [show τ.app (DerivedCategory.Q.obj P) ≫ ε.app P = β.app P from h]
      exact hβ P hP
    exact IsIso.of_isIso_comp_right _ (ε.app P)
  have (X : DerivedCategory A) : IsIso (τ.app X) := by
    obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage X)
    let : QuasiIso p := hp
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso τ e).1 (hi P hP)
  let := NatIso.isIso_of_isIso_app τ
  exact ⟨asIso τ⟩

attribute [local irreducible] diagonalScalarExtension diagonalFiniteToPadic
  diagonalScalarAdjunction

/-- Evaluation of simultaneous derived reduction factors through residue coefficients.
No endpoint identifications or Ext classes occur in this assertion.

Source: diagonal tower system proof, step (2), and evaluation in step (4)
(blueprint: lem-sfb-diagonal-residue-derived-factorization).

Proof: the projection from p-adic integers to the residue ring is surjective
with principal kernel generated by the positive prime power. The source library's
sheafified quotient construction gives an actual residue functor. Its restricted
projection and D.ordinary's level projection are cokernels of the same
multiplication map, so the unique cokernel comparisons form a natural isomorphism.
Use complexes with monic positive-prime-power multiplication as a common
resolving class. Flat-term K-flat resolutions resolve every complex by this class.
The multiplication/quotient short exact sequences show that tower reduction and
level reduction invert quasi-isomorphisms in the class. Exact faithful
restriction reflects quasi-isomorphisms, giving the same fact for residue
reduction. The existing cochain resolving-class construction derives all three
functors with counits invertible on this class. Uniqueness of left-derived
functors shows that D's counit is invertible there too. Compose the tower and
residue counits with the exact-functor comparisons for evaluation and restriction.
The level derived universal property compares each resulting functor to derived
level reduction. Each comparison is invertible on the resolving class, hence on
every derived object, because every such object is isomorphic to the localization
of a resolving complex. Composing the two comparisons gives the required
factorization. No invertibility of the prime on W is used. -/
theorem diagonal_residue_derived_factorization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (n : ℕ)
    [HasDerivedCategory.{wB} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{wC}
      (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) :
    ∃ R : DerivedCategory (DiagonalAb W) ⥤
        DerivedCategory
          (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))),
      Nonempty (R ⋙ (diagonalFiniteToPadic ℓ n W).mapDerivedCategory ≅
        D.T ⋙ ((evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)).mapDerivedCategory) := by
  let L := diagonalScalarExtension ℓ W
  let V := (evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)
  let F := diagonalFiniteToPadic ℓ n W
  let : L.Additive := scalarExtension_additive ℓ W
  let : PreservesFiniteLimits L := scalarExtension_exact ℓ W
  have : PreservesColimits L :=
    (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits L := inferInstance
  let : F.Full := by
    unfold F diagonalFiniteToPadic
    exact Sheaf.restrictScalars_full (Scheme.ProEt.topology W)
      (diagonalResidueProjection.{u} ℓ n) (diagonalResidueProjection_surjective ℓ n)
  have : F.Faithful := by unfold F diagonalFiniteToPadic; infer_instance
  let good : CochainComplex (DiagonalAb W) ℤ → Prop := fun P ↦
    ∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 (P.X i))
  have res : ∀ K : CochainComplex (DiagonalAb W) ℤ,
      ∃ (P : CochainComplex (DiagonalAb W) ℤ) (p : P ⟶ K), good P ∧ QuasiIso p := by
    intro K
    obtain ⟨P, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    refine ⟨P, p, ?_, hp⟩
    intro m i
    exact flat_multiplication_mono _
      (integerUnit_mono W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)
  have hm (P : CochainComplex (DiagonalAb W) ℤ) (hP : good P) (m : ℕ) (i : ℤ) :
      Mono (ℓ ^ (m + 1) • 𝟙 (L.obj (P.X i))) := by
    let := hP m i
    have h : Mono (L.map (ℓ ^ (m + 1) • 𝟙 (P.X i))) := inferInstance
    rw [Functor.map_nsmul, L.map_id] at h
    exact h
  have invsys {P Q : CochainComplex (DiagonalAb W) ℤ} (f : P ⟶ Q)
      (hf : QuasiIso f) (hP : good P) (hQ : good Q) :
      QuasiIso ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).map f) := by
    let := hf
    exact reductionTower_quasiIso ℓ L D.ordinary f (hm P hP) (hm Q hQ)
  have invlevel {P Q : CochainComplex (DiagonalAb W) ℤ} (f : P ⟶ Q)
      (hf : QuasiIso f) (hP : good P) (hQ : good Q) :
      QuasiIso (((D.ordinary.E ⋙ V).mapHomologicalComplex (.up ℤ)).map f) := by
    let := hf
    exact reductionLevel_quasiIso ℓ L D.ordinary n f (hm P hP n) (hm Q hQ n)
  obtain ⟨T, ε, hu, _, _, hc⟩ := cochainDerivedFullExists D.ordinary.E good res invsys
  let := hu
  let := D.universal
  let c := Functor.leftDerivedNatIso D.T T D.ε ε
    (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ)) (Iso.refl _)
  have hD (P : CochainComplex (DiagonalAb W) ℤ) (hP : good P) : IsIso (D.ε.app P) := by
    have h : c.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = D.ε.app P := by
      dsimp only [c, Functor.leftDerivedNatIso]
      simpa only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
        Functor.leftDerivedNatTrans_app D.T T D.ε ε
          (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ)) (𝟙 _) P
    let := hc P hP
    rw [← h]
    infer_instance
  obtain ⟨E, hE, ⟨θ⟩⟩ := ordinary_residue_factorization ℓ n W D.ordinary
  let := hE
  have invE {P Q : CochainComplex (DiagonalAb W) ℤ} (f : P ⟶ Q)
      (hf : QuasiIso f) (hP : good P) (hQ : good Q) :
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).1
    exact ((HomologicalComplex.quasiIso (DiagonalMod ℓ W) (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso (Functor.mapHomologicalComplexCompIso θ (.up ℤ))
        (Arrow.mk f))).2 (invlevel f hf hP hQ)
  obtain ⟨R, ρ, _, _, _, hρ⟩ := cochainDerivedFullExists E good res invE
  obtain ⟨Tn, εn, hun, _, _, hcn⟩ := cochainDerivedFullExists (D.ordinary.E ⋙ V)
    good res invlevel
  let := hun
  let β := mapped_counit D.ordinary.E D.T D.ε V
  obtain ⟨d⟩ := common_resolution_iso (D.ordinary.E ⋙ V) good res Tn εn hcn
    (D.T ⋙ V.mapDerivedCategory) β (by
      intro P hP
      let := hD P hP
      exact mapped_counit_isIso D.ordinary.E D.T D.ε V P)
  let β' := mapped_counit E R ρ F ≫
    Functor.whiskerRight (NatIso.mapHomologicalComplex θ (.up ℤ)).hom DerivedCategory.Q
  obtain ⟨r⟩ := common_resolution_iso (D.ordinary.E ⋙ V) good res Tn εn hcn
    (R ⋙ F.mapDerivedCategory) β' (by
      intro P hP
      let := hρ P hP
      let := mapped_counit_isIso E R ρ F P
      dsimp only [β', NatTrans.comp_app]
      infer_instance)
  exact ⟨R, ⟨r ≪≫ d.symm⟩⟩

end AlgebraicGeometry.ProEtale
