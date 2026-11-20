import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiFiniteProjectiveStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeStatement
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Eventual locally quasi-finite maps to projective space from torsion bracket maps and
the determination of data by their torsion configurations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A Jacobson space with finitely many closed points is finite. -/
theorem finite_of_jacobsonSpace_of_finite_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] (h : (closedPoints X).Finite) : Finite X := by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints,
      closure_subset_iff_isClosed, ← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ ↦ id
  exact Set.finite_univ_iff.mp (this ▸ h)

set_option backward.isDefEq.respectTransparency.types false in
/-- For a morphism `f` locally of finite type, every closed point `z` of the fibre of `f`
over `y` comes from a geometric point of `X` over the algebraic closure of `κ(y)` lying over
`y`, whose underlying point is the image of `z` in `X`. -/
theorem exists_geometricPoint_of_mem_closedPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) (z : f.fiber y) (hz : z ∈ closedPoints (f.fiber y)) :
    ∃ t : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X,
      t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y ∧
        t (IsLocalRing.closedPoint _) = f.fiberι y z := by
  have : IsClosedImmersion ((f.fiber y).fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let g := (f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y
  have hg : IsFinite g :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := g)).mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    exact hg
  let _ := φ.hom.toAlgebra
  have : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := hfin
  let ψ : (f.fiber y).residueField z →ₐ[Y.residueField y]
      AlgebraicClosure (Y.residueField y) := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (f.fiber y).fromSpecResidueField z ≫
    f.fiberι y, ?_, ?_⟩
  · have h1 : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap
        (Y.residueField y) (AlgebraicClosure (Y.residueField y))) := by
      ext x
      exact ψ.commutes x
    calc _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g ≫ Y.fromSpecResidueField y := by
          simp only [g, Category.assoc, Scheme.Hom.fiber_fac]
      _ = _ := by
        rw [← hφ, ← Category.assoc, ← Spec.map_comp]
        erw [h1]
  · simp only [Scheme.Hom.comp_apply]
    rw [Scheme.fromSpecResidueField_apply]

/-- A morphism locally of finite type with finitely many geometric points over every
geometric point of the target has finite set-theoretic fibres. -/
theorem finite_preimage_singleton_of_finite_geometricFibres {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (hf : ∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (CommRingCat.of K) ⟶ Y),
      {x : Spec (CommRingCat.of K) ⟶ X | x ≫ f = y}.Finite) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have hcl : (closedPoints (f.fiber y)).Finite := by
    choose t ht using exists_geometricPoint_of_mem_closedPoints f y
    have hfin := hf (AlgebraicClosure (Y.residueField y)) (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y)
    have : Finite {x : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X |
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y} :=
      hfin.to_subtype
    let F : closedPoints (f.fiber y) → {x : Spec (CommRingCat.of
        (AlgebraicClosure (Y.residueField y))) ⟶ X | x ≫ f = Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y} :=
      fun z => ⟨t z.1 z.2, (ht z.1 z.2).1⟩
    have hF : Function.Injective F := by
      rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
      have h' : t z hz = t z' hz' := congrArg Subtype.val h
      have h'' : f.fiberι y z = f.fiberι y z' := by
        rw [← (ht z hz).2, ← (ht z' hz').2, h']
      exact Subtype.ext ((f.fiberι y).isEmbedding.injective h'')
    have : Finite (closedPoints (f.fiber y)) := Finite.of_injective F hF
    exact Set.toFinite _
  have : Finite (f.fiber y) := finite_of_jacobsonSpace_of_finite_closedPoints hcl
  rw [← f.range_fiberι y]
  exact Set.finite_range _

/-- A morphism locally of finite type with finitely many geometric points over every
geometric point of the target is locally quasi-finite. -/
theorem locallyQuasiFinite_of_finite_geometricFibres {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (hf : ∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (CommRingCat.of K) ⟶ Y),
      {x : Spec (CommRingCat.of K) ⟶ X | x ≫ f = y}.Finite) :
    LocallyQuasiFinite f :=
  LocallyQuasiFinite.of_finite_preimage_singleton f
    (finite_preimage_singleton_of_finite_geometricFibres f hf)

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Over a level base representing the moduli functor, two field-valued points along which
the pullbacks of a universal datum are isomorphic are equal. -/
theorem eq_of_isomorphic_pullback {P : Prerequisites.{0}} {g d n : ℕ} {hd : 0 < d}
    {hn : 3 ≤ n} {X : LevelBase n} (e : uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn)
    (b : Datum P X.obj g d n)
    (hb : b.classOf = e.hom.app (Opposite.op X) (ULift.up (𝟙 X)))
    {K : Type} [Field K] (t t' : Spec (CommRingCat.of K) ⟶ X.obj)
    (h : Isomorphic (b.pullback t) (b.pullback t')) : t = t' := by
  have hunitK : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast t.appTop.hom n]
    exact X.level_isUnit.map _
  let TK : LevelBase n := LevelBase.ofScheme (Spec (CommRingCat.of K)) hunitK
  have key : ∀ s : Spec (CommRingCat.of K) ⟶ X.obj,
      e.hom.app (Opposite.op TK) (ULift.up (LevelBase.homMk (S := TK) (T := X) s)) =
        (b.pullback s).classOf := by
    intro s
    have h1 := NatTrans.naturality_apply e.hom (LevelBase.homMk (S := TK) (T := X) s).op
      (ULift.up (𝟙 X) : ULift (X ⟶ X))
    have h3 : (uliftYoneda.{1}.obj X).map (LevelBase.homMk (S := TK) (T := X) s).op
        (ULift.up (𝟙 X) : ULift (X ⟶ X)) =
          ULift.up (LevelBase.homMk (S := TK) (T := X) s) := by
      rfl
    rw [h3, ← hb, moduliFunctor_map_classOf] at h1
    exact h1
  have hx : e.hom.app (Opposite.op TK) (ULift.up (LevelBase.homMk (S := TK) (T := X) t)) =
      e.hom.app (Opposite.op TK) (ULift.up (LevelBase.homMk (S := TK) (T := X) t')) := by
    rw [key, key]
    exact Quotient.sound h
  have hy := (CategoryTheory.mono_iff_injective (e.hom.app (Opposite.op TK))).1
    inferInstance hx
  exact congrArg (fun z => z.down.hom) hy

set_option linter.defProp false in
/-- Proved definition: eventual local finite type of representing level bases, torsion
bracket maps with finitely many torsion configurations in each geometric fibre, and the
determination of data by their torsion configurations over algebraically closed fields (in
universe zero) imply `LargeLevelQuasiFiniteProjectiveStatement`. In each geometric fibre of
the bracket map of the universal datum, the points fall into finitely many configuration
classes. Determination and the representing isomorphism make each class a single point, and
local finite type turns finite geometric fibres into local quasi-finiteness. -/
def largeLevelQuasiFiniteProjective_of_torsionBrackets
    (Hft : LargeLevelFiniteTypeStatement) (Hb : TorsionBracketMapStatement)
    (Hr : TorsionConfigurationDeterminationStatement.{0}) :
    LargeLevelQuasiFiniteProjectiveStatement := by
  intro P g d hg hd
  obtain ⟨N₁, hN₁⟩ := Hft P g d hg hd
  obtain ⟨N₂, hN₂⟩ := Hb P g d hg hd
  obtain ⟨N₃, hN₃⟩ := Hr P g d hg hd
  refine ⟨max N₁ (max N₂ N₃), fun n hn' hn X ⟨e⟩ => ?_⟩
  have h₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn'
  have h₂ : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn'
  have h₃ : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn'
  have : LocallyOfFiniteType X.toLocalizationSpec := (hN₁ n h₁ hn X ⟨e⟩).1
  obtain ⟨b, hb⟩ := Quotient.exists_rep
    (e.hom.app (Opposite.op X) (ULift.up (𝟙 X)) : Moduli P X.obj g d n)
  obtain ⟨m, j, hj⟩ := hN₂ n h₂ X b
  have hjp : j ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec
      (Localization.Away (n : ℤ)) m = X.toLocalizationSpec := X.eq_toLocalizationSpec _
  refine ⟨m, j, ?_, hjp⟩
  have : LocallyOfFiniteType (j ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec
      (Localization.Away (n : ℤ)) m) := by
    rw [hjp]
    infer_instance
  have : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j
    (Langlands.AlgebraicGeometry.projectiveSpaceToSpec (Localization.Away (n : ℤ)) m)
  apply Langlands.AlgebraicGeometry.locallyQuasiFinite_of_finite_geometricFibres
  intro K _ _ y
  obtain ⟨s, hs⟩ := hj K y
  refine s.finite_toSet.subset fun t ht => ?_
  obtain ⟨t', ht', hc⟩ := hs t ht
  have hunitK : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast t.appTop.hom n]
    exact X.level_isUnit.map _
  have hunit : IsUnit (n : K) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom n]
    exact hunitK.map _
  have hiso := hN₃ n h₃ K hunit.ne_zero _ _ hc
  rw [eq_of_isomorphic_pullback e b hb t t' hiso]
  exact ht'

end Langlands.AbelianScheme.PolarizedFiniteLevel
