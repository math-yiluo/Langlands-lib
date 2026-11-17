import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.DiscreteGaloisFiniteFactorizationProof
import Langlands.GroupScheme.Torus.GaloisModuleRealizationProof
import Langlands.GroupScheme.Descent.GaloisHom
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Reductive.StarActionFiniteStageTower

/-! # The absolute-Galois character anti-equivalence: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace MultiplicativeTypeAbsoluteEquivalence

open MultiplicativeTypeGaloisFullFaithfulness MultiplicativeTypeSplitting

section Separation

variable {k : Type u} [Field k]

/-- Over the separable closure, a group of multiplicative type is isomorphic to the
diagonalizable group of some abelian group. -/
theorem exists_iso_diagonalizable (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsMultiplicativeType T.toGrp) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ),
      Nonempty ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T ≅
        Diagonalizable.groupScheme (CommRingCat.of (SeparableClosure k)) Λ) := by
  obtain ⟨Λ, hΛ, -, ⟨e⟩⟩ := isFGDiagonalizable_of_isSepClosed _
    (isMultiplicativeType_baseChange_of_isAlgebraic k (SeparableClosure k) T.toGrp hT)
  exact ⟨Λ, hΛ, ⟨CommGroupScheme.isoOfGroupIso e⟩⟩

/-- Scalar extension along a field extension is injective on homomorphisms. -/
theorem baseChange_map_injective (L : Type u) [Field L] [Algebra k L]
    {G H : CommGroupScheme (Spec (CommRingCat.of k))} {f g : G ⟶ H}
    (h : (CommGroupScheme.baseChange (algebraBaseMap k L)).map f =
      (CommGroupScheme.baseChange (algebraBaseMap k L)).map g) : f = g := by
  let b := algebraBaseMap k L
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  have hg : CommGroupScheme.groupHom f = CommGroupScheme.groupHom g := by
    apply Grp.hom_ext
    apply (Over.pullback b).map_injective
    change ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom f)).hom.hom =
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom g)).hom.hom
    exact congrArg (fun φ => (CommGroupScheme.groupHom φ).hom.hom) h
  exact congrArg Additive.ofMul hg

/-- Equivariance of character pullback makes a homomorphism over an arbitrary Galois
extension satisfy the canonical descent compatibility, when the target becomes
diagonalizable. -/
theorem descent_compat_of_equivariant (L : Type u) [Field L] [Algebra k L]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))} {Λ' : Type u} [AddCommGroup Λ']
    (i' : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T' ≅
      Diagonalizable.groupScheme (CommRingCat.of L) Λ')
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')
    (hf : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
        f ≫ characterLattice.galoisRepresentation k L T' σ χ)
    (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map (CommGroupScheme.groupHom f) ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) T'.toGrp).hom =
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T.toGrp).hom ≫ CommGroupScheme.groupHom f := by
  have h := congrArg CommGroupScheme.groupHom
    (galoisHomTransport_eq_of_diagonalizable i' f hf σ)
  change (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T.toGrp).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map (CommGroupScheme.groupHom f) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T'.toGrp).hom = CommGroupScheme.groupHom f at h
  rwa [Iso.inv_comp_eq] at h

end Separation

section FiniteLevel

/-- The base change of an evaluation character of a diagonalizable group is the evaluation
character of the base-changed diagonalizable group. -/
theorem baseChange_evalCharacter {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
    (Λ : Type u) [AddCommGroup Λ] (m : Λ) :
    characterLattice.baseChange b _ (DiagonalizableCharacter.evalCharacter R Λ m) =
      (Diagonalizable.commBaseChangeIso b Λ).hom ≫
        DiagonalizableCharacter.evalCharacter R' Λ m := by
  apply characterLattice.ext_points
  intro U z
  rw [StarActionFiniteStage.characterLattice_baseChange_points,
    DiagonalizableCharacter.evalCharacter_apply, comp_groupHom_comp,
    DiagonalizableCharacter.evalCharacter_apply]
  change _ = Diagonalizable.characterPointsEquiv R' Λ U
    (z ≫ (Diagonalizable.baseChangeIso b Λ).hom.hom.hom) _
  rw [Diagonalizable.characterPointsEquiv_baseChangeIso_hom]
  rfl

variable {k : Type u} [Field k]

/-- The base maps of a tower of fields compose. -/
theorem algebraBaseMap_tower (L Ω : Type u) [Field L] [Field Ω] [Algebra k L] [Algebra k Ω]
    [Algebra L Ω] [IsScalarTower k L Ω] :
    algebraBaseMap L Ω ≫ algebraBaseMap k L = algebraBaseMap k Ω := by
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k L Ω).symm

/-- Restriction to a normal intermediate field is compatible with the base maps. -/
theorem galoisBaseMap_restrictNormal (L : IntermediateField k (SeparableClosure k))
    [Normal k L] (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    algebraBaseMap L (SeparableClosure k) ≫
        galoisBaseMap k L (AlgEquiv.restrictNormalHom L σ) =
      galoisBaseMap k (SeparableClosure k) σ ≫ algebraBaseMap L (SeparableClosure k) := by
  unfold galoisBaseMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact AlgEquiv.restrictNormal_commutes σ L x

/-- **Finite-level realization, read over the separable closure.** A finitely generated
module for the Galois group of a finite Galois subextension `L` of the separable closure is,
after inflation, the actual separable-closure character module of a group of multiplicative
type. -/
theorem exists_absolute_realization (L : IntermediateField k (SeparableClosure k))
    [FiniteDimensional k L] [IsGalois k L]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M] (ρ : Representation ℤ (L ≃ₐ[k] L) M) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (_ : IsMultiplicativeType T.toGrp)
      (Φ : M ≃+ characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T)),
      ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (m : M),
        Φ (ρ (AlgEquiv.restrictNormalHom L σ) m) =
          characterLattice.galoisRepresentation k (SeparableClosure k) T σ (Φ m) := by
  obtain ⟨T, i, e, hpts, he⟩ := multiplicativeTypeGaloisModuleRealization k L M ρ
  have hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
      algebraBaseMap k (SeparableClosure k) := algebraBaseMap_tower L (SeparableClosure k)
  have hT : IsMultiplicativeType T.toGrp :=
    ⟨L, inferInstance, inferInstance, M, inferInstance, inferInstance,
      ⟨{ hom := CommGroupScheme.groupHom i.hom
         inv := CommGroupScheme.groupHom i.inv
         hom_inv_id := congrArg CommGroupScheme.groupHom i.hom_inv_id
         inv_hom_id := congrArg CommGroupScheme.groupHom i.inv_hom_id }⟩⟩
  let ψ := StarActionFiniteStage.towerIsoOf (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) T (algebraBaseMap k (SeparableClosure k)) hc ≪≫
    (CommGroupScheme.baseChange (algebraBaseMap L (SeparableClosure k))).mapIso i ≪≫
      Diagonalizable.commBaseChangeIso (algebraBaseMap L (SeparableClosure k)) M
  let Φ : M ≃+ characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T) :=
    (DiagonalizableCharacter.evalCharacterEquiv (SeparableClosure k) M).trans
      (characterLattice.congr ψ).symm
  have hem : ∀ m, e m = i.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of L) M m := by
    intro m
    apply characterLattice.ext_points
    intro U x
    rw [hpts m U x, comp_groupHom_comp, DiagonalizableCharacter.evalCharacter_apply]
  have hτ : ∀ m, StarActionFiniteStage.towerCharacterOf (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) T (algebraBaseMap k (SeparableClosure k)) hc
        (e m) = Φ m := by
    intro m
    change (StarActionFiniteStage.towerIsoOf (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) T (algebraBaseMap k (SeparableClosure k))
        hc).hom ≫ characterLattice.baseChange (algebraBaseMap L (SeparableClosure k)) _ (e m) =
      ψ.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of (SeparableClosure k)) M m
    rw [hem m, characterLattice.baseChange_precomp, baseChange_evalCharacter]
    simp only [ψ, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  refine ⟨T, hT, Φ, fun σ m => ?_⟩
  rw [← hτ (ρ (AlgEquiv.restrictNormalHom L σ) m), ← hτ m, he,
    characterLattice.galoisRepresentation_apply,
    StarActionFiniteStage.towerCharacterOf_transport (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) T (algebraBaseMap k (SeparableClosure k)) hc _ _
      (galoisBaseMap k (SeparableClosure k) σ) (galoisBaseMap_over k (SeparableClosure k) σ)
      (galoisBaseMap_restrictNormal L σ)]
  rfl

end FiniteLevel

end MultiplicativeTypeAbsoluteEquivalence

open MultiplicativeTypeAbsoluteEquivalence MultiplicativeTypeGaloisFullFaithfulness

namespace MultiplicativeTypeGroup

variable (k : Type u) [Field k]

instance characterFunctor_faithful : (characterFunctor k).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨Λ, _, ⟨i⟩⟩ := exists_iso_diagonalizable X.unop.obj X.unop.property
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply baseChange_map_injective (SeparableClosure k)
    apply hom_ext_of_iso_diagonalizable i
    intro χ
    have := congrArg (fun φ => FGDiscreteGaloisModule.hom φ χ) h
    simpa only [characterFunctor_map_apply] using this

instance characterFunctor_full : (characterFunctor k).Full where
  map_surjective {X Y} φ := by
    obtain ⟨Λ, _, ⟨i⟩⟩ := exists_iso_diagonalizable X.unop.obj X.unop.property
    obtain ⟨Λ', _, ⟨i'⟩⟩ := exists_iso_diagonalizable Y.unop.obj Y.unop.property
    obtain ⟨f, hfF⟩ := exists_hom_of_characterMap i' i
      (FGDiscreteGaloisModule.hom φ).toLinearMap.toAddMonoidHom
    have hf : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
        (χ : characterLattice ((CommGroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj X.unop.obj)),
        characterLattice.galoisRepresentation k (SeparableClosure k) Y.unop.obj σ (f ≫ χ) =
          f ≫ characterLattice.galoisRepresentation k (SeparableClosure k) X.unop.obj σ χ := by
      intro σ χ
      rw [hfF, hfF]
      exact (LinearMap.congr_fun ((FGDiscreteGaloisModule.hom φ).isIntertwining' σ) χ).symm
    have : IsAffineHom Y.unop.obj.X.hom := Y.unop.property.isAffineHom
    have : IsAffineHom X.unop.obj.X.hom := X.unop.property.isAffineHom
    have hc := descent_compat_of_equivariant (SeparableClosure k) i f hf
    let a : Y.unop.obj ⟶ X.unop.obj := Additive.ofMul
      (Descent.GaloisHom.hom (CommGroupScheme.groupHom f) hc)
    have ha : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map a = f :=
      congrArg Additive.ofMul (Descent.GaloisHom.baseChange_hom (CommGroupScheme.groupHom f) hc)
    refine ⟨(ObjectProperty.homMk a : Y.unop ⟶ X.unop).op, ?_⟩
    rw [← FGDiscreteGaloisModule.ofHom_hom ((characterFunctor k).map _),
      ← FGDiscreteGaloisModule.ofHom_hom φ]
    congr 1
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro χ
    change (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map a ≫ χ = _
    rw [ha]
    exact hfF χ


instance characterFunctor_essSurj : (characterFunctor k).EssSurj where
  mem_essImage A := by
    obtain ⟨L, hfin, hgal, ρL, hρL⟩ :=
      discreteGaloisFiniteFactorization k A A.representation A.isSmooth
    have hfg : AddGroup.FG A := by
      have h : Module.Finite ℤ A := inferInstance
      exact Module.Finite.iff_addGroup_fg.mp (by convert h; exact Subsingleton.elim _ _)
    obtain ⟨T, hT, Φ, hΦ⟩ := exists_absolute_realization L A
      { toFun := fun g => (ρL g).toAddMonoidHom.toIntLinearMap
        map_one' := DFunLike.ext _ _ fun m => by
          change (ρL 1) m = m
          rw [map_one]
          rfl
        map_mul' := fun g h => DFunLike.ext _ _ fun m => by
          change (ρL (g * h)) m = (ρL g) ((ρL h) m)
          rw [map_mul]
          rfl }
    have hA : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (m : A),
        A.representation σ m = ρL (AlgEquiv.restrictNormalHom L σ) m := by
      intro σ m
      rw [← hρL]
      rfl
    have h2 : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (m : A),
        Φ (A.representation σ m) =
          characterLattice.galoisRepresentation k (SeparableClosure k) T σ (Φ m) := by
      intro σ m
      rw [hA]
      exact hΦ σ m
    have h1 : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) χ,
        Φ.symm (characterLattice.galoisRepresentation k (SeparableClosure k) T σ χ) =
          A.representation σ (Φ.symm χ) := by
      intro σ χ
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply, Φ.apply_symm_apply]
    have hext : ∀ {X Y : FGDiscreteGaloisModule.{u, u} k} {f g : X ⟶ Y},
        (∀ x, FGDiscreteGaloisModule.hom f x = FGDiscreteGaloisModule.hom g x) → f = g :=
      fun h => congrArg FGDiscreteGaloisModule.ofHom
        (Representation.IntertwiningMap.ext (LinearMap.ext h))
    refine ⟨op ⟨T, hT⟩, ⟨?_⟩⟩
    exact
      { hom := FGDiscreteGaloisModule.ofHom
          (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
            Φ.symm.toIntLinearEquiv.toLinearMap h1)
        inv := FGDiscreteGaloisModule.ofHom
          (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
            Φ.toIntLinearEquiv.toLinearMap h2)
        hom_inv_id := hext fun χ => Φ.apply_symm_apply χ
        inv_hom_id := hext fun m => Φ.symm_apply_apply m }

end MultiplicativeTypeGroup

/-- **The absolute-Galois character anti-equivalence.** For every field `k`, the actual
separable-closure character functor on groups of multiplicative type over `k` is an
equivalence onto finitely generated discrete modules for the absolute Galois group. -/
theorem multiplicativeTypeAbsoluteEquivalence :
    MultiplicativeTypeAbsoluteEquivalenceStatement.{u} := fun _ _ => { }

end Langlands.GroupScheme
