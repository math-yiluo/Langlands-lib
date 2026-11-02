import Langlands.AlgebraicGeometry.RingEtaleGroupoidStableSubalgebra
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianCoaction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianDiagram
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

/-! # Cofiltered systems of finitely generated stable levels -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

namespace Langlands.AlgebraicGeometry.RingEtaleGroupoid.StableSystem

open EtaleEquivalenceRelation

variable {B₀ C₀ B : Type u} [CommRing B₀] [CommRing C₀] [CommRing B]
  [Algebra B₀ C₀] [Algebra B₀ B] {t₀ : B₀ →+* C₀}
  (hE : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ B) (hθ : θ.IsMultiplicative)

/-- The finitely generated stable subalgebras, ordered by inclusion. -/
abbrev Index := {S : Subalgebra B₀ B // S.FG ∧ θ.IsStableSubalgebra S}

/-- The subalgebra at an index, as a monotone family. -/
def subalgebra : Index θ →o Subalgebra B₀ B where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

include hE hθ in
/-- Every finitely generated subalgebra lies in a stable finitely generated one. -/
lemma exists_ge [IsNoetherianRing B₀] (S : Subalgebra B₀ B) (hS : S.FG) :
    ∃ i : Index θ, S ≤ i.1 := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨T, hT, hst, hstable⟩ := hE.exists_fg_stableSubalgebra θ hθ s
  refine ⟨⟨T, hT, hstable⟩, ?_⟩
  rw [← hs]
  exact Algebra.adjoin_le hst

include hE hθ in
/-- The stable index is nonempty. -/
lemma indexNonempty [IsNoetherianRing B₀] : Nonempty (Index θ) := by
  obtain ⟨i, _⟩ := exists_ge hE θ hθ ⊥ Subalgebra.fg_bot
  exact ⟨i⟩

include hE hθ in
/-- The stable index is directed. -/
lemma indexDirected [IsNoetherianRing B₀] : IsDirected (Index θ) (· ≤ ·) := by
  constructor
  intro i j
  obtain ⟨k, hk⟩ := exists_ge hE θ hθ (i.1 ⊔ j.1) (i.2.1.sup j.2.1)
  exact ⟨k, le_sup_left.trans hk, le_sup_right.trans hk⟩

include hE hθ in
/-- Its opposite is a cofiltered category in the same universe. -/
lemma indexCofiltered [IsNoetherianRing B₀] : IsCofiltered (Index θ)ᵒᵖ := by
  let := indexNonempty hE θ hθ
  let := indexDirected hE θ hθ
  infer_instance

include hE hθ in
/-- The subalgebra family exhausts the original ring. -/
lemma exhaustive [IsNoetherianRing B₀] (b : B) :
    ∃ i : Index θ, b ∈ subalgebra θ i := by
  obtain ⟨S, hS, hs, hstable⟩ := hE.exists_fg_stableSubalgebra θ hθ {b}
  exact ⟨⟨S, hS, hstable⟩, hs (by simp)⟩

instance (i : Index θ) : Algebra.FiniteType B₀ i.1 :=
  (Subalgebra.fg_iff_finiteType i.1).mp i.2.1

instance [IsNoetherianRing B₀] (i : Index θ) : IsNoetherianRing i.1 := by
  let : Algebra.FiniteType B₀ i.1 := (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  exact Algebra.FiniteType.isNoetherianRing B₀ i.1

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The relation at a stable finite level. -/
noncomputable def level (i : Index θ) : EtaleEquivalenceRelation.{u} :=
  (hE.level (hE.subalgebraCoaction θ i.1 i.2.2)
    (hE.subalgebraCoaction_isMultiplicative θ hθ i.1 i.2.2)).toScheme

instance (i : Index θ) : IsAffine (level hE θ hθ i).U :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of i.1)))

instance (i : Index θ) : IsAffine (level hE θ hθ i).R :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (C₀ ⊗[B₀] i.1))))

instance [IsNoetherianRing B₀] (i : Index θ) : IsNoetherian (level hE θ hθ i).U :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of i.1)))

/-- Finite type over the integers is retained at every stable finite level. -/
lemma finiteType_int [Algebra.FiniteType ℤ B₀] (i : Index θ) :
    Algebra.FiniteType ℤ i.1 :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ B₀)
    (inferInstance : Algebra.FiniteType B₀ i.1)

/-- Inclusion between stable levels is equivariant. -/
lemma inclusion_equivariant {i j : Index θ} (h : i ≤ j) (b : i.1) :
    Algebra.TensorProduct.map (AlgHom.id B₀ C₀) (Subalgebra.inclusion h)
        ((hE.subalgebraCoaction θ i.1 i.2.2).coaction b) =
      (hE.subalgebraCoaction θ j.1 j.2.2).coaction (Subalgebra.inclusion h b) := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) j.1.val :
        C₀ ⊗[B₀] j.1 → C₀ ⊗[B₀] B) := by
    intro x y hxy
    apply hE.lTensor_val_injective j.1
    rw [lTensor_eq_map, lTensor_eq_map, hxy]
  apply hinj
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp]
  change Algebra.TensorProduct.map (AlgHom.id B₀ C₀) i.1.val
      ((hE.subalgebraCoaction θ i.1 i.2.2).coaction b) =
    Algebra.TensorProduct.map (AlgHom.id B₀ C₀) j.1.val
      ((hE.subalgebraCoaction θ j.1 j.2.2).coaction (Subalgebra.inclusion h b))
  rw [subalgebraCoaction_val, subalgebraCoaction_val]
  rfl

/-- The actual cartesian transition between stable levels. -/
noncomputable def transition {i j : Index θ} (h : i ≤ j) :
    level hE θ hθ j ⟶ level hE θ hθ i where
  objMap := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)
  relMap := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) (Subalgebra.inclusion h)).toRingHom)
  isCartesian := isCartesianHom_of_equivariant _ _ (Subalgebra.inclusion h)
    (inclusion_equivariant hE θ h)

/-- The inverse system of stable finite levels. -/
noncomputable def diagram : (Index θ)ᵒᵖ ⥤ EtaleEquivalenceRelation.{u} where
  obj i := level hE θ hθ i.unop
  map a := transition hE θ hθ a.unop.le
  map_id i := by
    apply CartesianMorphism.ext
    · change Spec.map _ = 𝟙 _
      rw [← Spec.map_id]
      rfl
    · change Spec.map _ = 𝟙 _
      rw [← Spec.map_id]
      congr 1
      ext c <;> rfl
  map_comp a b := by
    apply CartesianMorphism.ext
    · change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      rfl
    · change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext c <;> rfl

/-- Comparison from the full coaction relation to a stable finite level. -/
noncomputable def coneMorphism (i : Index θ) :
    (hE.level θ hθ).toScheme ⟶ level hE θ hθ i where
  objMap := Spec.map (CommRingCat.ofHom i.1.val.toRingHom)
  relMap := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) i.1.val).toRingHom)
  isCartesian := isCartesianHom_of_equivariant _ _ i.1.val
    (hE.subalgebraCoaction_val θ i.1 i.2.2)

/-- The original coaction relation is the point of the stable level cone. -/
noncomputable def cone : Cone (diagram hE θ hθ) where
  pt := (hE.level θ hθ).toScheme
  π :=
    { app i := coneMorphism hE θ hθ i.unop
      naturality i j a := by
        change (𝟙 _ : (hE.level θ hθ).toScheme ⟶ _) ≫ _ = _ ≫ _
        rw [Category.id_comp]
        apply CartesianMorphism.ext
        · change Spec.map _ = Spec.map _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl
        · change Spec.map _ = Spec.map _ ≫ Spec.map _
          rw [← Spec.map_comp]
          congr 1
          ext c <;> rfl }

/-- The object schemes of the stable levels have the actual original spectrum
as their limit. -/
noncomputable def isLimitObject [IsNoetherianRing B₀] :
    IsLimit (objectFunctor.mapCone (cone hE θ hθ)) := by
  letI := indexNonempty hE θ hθ
  letI := indexDirected hE θ hθ
  exact (P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isLimit_specCone
    (subalgebra θ) (exhaustive hE θ hθ)).some

end Langlands.AlgebraicGeometry.RingEtaleGroupoid.StableSystem

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom

open RingEtaleGroupoid

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {E E₀ : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ E₀.U} {g : E.R ⟶ E₀.R}
  (h : IsCartesianHom E E₀ f g) [IsAffine E.U] [IsAffine E₀.U] [IsAffine E₀.R]

/-- Stable finite levels indexed by the actual coordinate ring of the original relation. -/
noncomputable abbrev stableIndex :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  StableSystem.Index h.coaction

/-- The actual cartesian diagram attached to an affine cartesian first level. -/
noncomputable def stableDiagram : (h.stableIndex)ᵒᵖ ⥤ EtaleEquivalenceRelation.{u} :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  StableSystem.diagram E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative

/-- The stable-level diagram of a Noetherian first level is cofiltered. -/
lemma stableIndex_isCofiltered [IsNoetherianRing Γ(E₀.U, ⊤)] :
    IsCofiltered (h.stableIndex)ᵒᵖ := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  exact StableSystem.indexCofiltered E₀.ringEtaleGroupoid h.coaction
    h.coaction_isMultiplicative

instance (i : (h.stableIndex)ᵒᵖ) : IsAffine (h.stableDiagram.obj i).U := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  exact inferInstanceAs (IsAffine
    (StableSystem.level E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative i.unop).U)

instance (i : (h.stableIndex)ᵒᵖ) : IsAffine (h.stableDiagram.obj i).R := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  exact inferInstanceAs (IsAffine
    (StableSystem.level E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative i.unop).R)

instance [IsNoetherianRing Γ(E₀.U, ⊤)] (i : (h.stableIndex)ᵒᵖ) :
    IsNoetherian (h.stableDiagram.obj i).U := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  exact inferInstanceAs (IsNoetherian
    (StableSystem.level E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative i.unop).U)

/-- The cartesian comparison from the original relation to its full coordinate-ring model. -/
noncomputable def toFullStableRelation :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    E ⟶ (E₀.ringEtaleGroupoid.level h.coaction h.coaction_isMultiplicative).toScheme :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  letI := h.isAffine_R
  { objMap := E.U.isoSpec.hom
    relMap := E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom
    isCartesian := h.isCartesianHom_toScheme }

/-- The original relation itself, with its actual object and arrow schemes, is the point
of the stable finite-level cone. -/
noncomputable def stableCone : Cone h.stableDiagram :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  (StableSystem.cone E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative).extend
    h.toFullStableRelation

/-- The original object scheme is the limit of the stable finite object schemes. -/
noncomputable def stableCone_isLimitObject [IsNoetherianRing Γ(E₀.U, ⊤)] :
    IsLimit (objectFunctor.mapCone h.stableCone) := by
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  apply IsLimit.ofIsoLimit
    (StableSystem.isLimitObject E₀.ringEtaleGroupoid h.coaction h.coaction_isMultiplicative)
  refine Cone.ext E.U.isoSpec.symm ?_
  intro i
  change Spec.map (CommRingCat.ofHom i.unop.1.val.toRingHom) =
    E.U.isoSpec.inv ≫
      (E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom i.unop.1.val.toRingHom))
  simp

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.IsCartesianHom
