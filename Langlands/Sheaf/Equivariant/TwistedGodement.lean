import Langlands.Sheaf.Equivariant.TwistedOver
import Langlands.Sheaf.Equivariant.LocalActionDiscretePart
import Langlands.Sheaf.Godement

/-!
# Godement constructions on a twisted site

Let `G` act on `X` and let `J` be a translation-invariant topology on
`P.Over ⊤ X`. The inclusion `ι` of `P.Over ⊤ X` into the twisted category is
continuous and cocontinuous, so restriction of sheaves along `ι` has a right
adjoint, the induction `ι_*` given by right Kan extension. For a family of points
of `J`, the degree-zero Godement functor of the twisted site is
`F ↦ ι_* C⁰(ι^* F)`, where `C⁰` is the Godement functor of `J`; it is Berkovich's
`ν_* ν^*` for the morphism of sites from the discrete family of points. Its
coaugmentation is monic when the fibers are jointly faithful, and iterated
cokernels give the Godement complex. On discrete sheaves for a local action
system, the discrete part of this functor gives the Godement construction among
discrete sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite

universe w wI v u uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]

section Induction

variable (A : Type uA) [Category.{vA} A]

/-- Restriction of sheaves to `P.Over ⊤ X` is faithful: every object of the twisted
category is an object of `P.Over ⊤ X`. -/
instance restriction_faithful : (restriction ρ J A).Faithful where
  map_injective {F F'} φ ψ h := by
    apply Sheaf.hom_ext
    ext ⟨U⟩
    exact NatTrans.congr_app (Sheaf.hom_ext_iff.1 h) (op U.obj)

omit [P.RespectsIso] [IsTranslationInvariant (ρ := ρ) J] in
/-- Module presheaves in a universe containing the objects and morphisms of `C` and
the group have right Kan extensions along the inclusion. -/
theorem hasPointwiseRightKanExtension_moduleCat (R : Type (max u v uG)) [CommRing R]
    (F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{max u v uG} R) :
    (ι P ρ).op.HasPointwiseRightKanExtension F :=
  inferInstance

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- Induction of sheaves from `P.Over ⊤ X` to the twisted site: the right Kan
extension along the inclusion. -/
abbrev induction : Sheaf J A ⥤ Sheaf (twistedTopology ρ J) A :=
  (ι P ρ).sheafPushforwardCocontinuous A J (twistedTopology ρ J)

/-- Restriction is left adjoint to induction. -/
def restrictionAdjunction : restriction ρ J A ⊣ induction ρ J A :=
  (ι P ρ).sheafAdjunctionCocontinuous A J (twistedTopology ρ J)

instance : (induction ρ J A).IsRightAdjoint :=
  (restrictionAdjunction ρ J A).isRightAdjoint

/-- The unit of the adjunction is a monomorphism. -/
instance mono_restrictionAdjunction_unit_app (F : Sheaf (twistedTopology ρ J) A) :
    Mono ((restrictionAdjunction ρ J A).unit.app F) :=
  inferInstance

end Induction

section Godement

variable {I : Type wI} (points : I → GrothendieckTopology.Point.{w} J)
variable (A : Type uA) [Category.{vA} A]
variable [HasProducts.{w} A] [HasProducts.{wI} A] [HasColimitsOfSize.{w, w} A]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The degree-zero Godement functor of the twisted site: restrict, apply the
Godement functor of `J`, and induce back. -/
def twistedZeroFunctor :
    Sheaf (twistedTopology ρ J) A ⥤ Sheaf (twistedTopology ρ J) A :=
  restriction ρ J A ⋙ Godement.zeroFunctor points A ⋙ induction ρ J A

/-- The coaugmentation: the unit of the restriction–induction adjunction followed
by the induction of the Godement coaugmentation of `J`. -/
def twistedCoaugmentation : 𝟭 _ ⟶ twistedZeroFunctor ρ J points A where
  app F := (restrictionAdjunction ρ J A).unit.app F ≫
    (induction ρ J A).map ((Godement.coaugmentation points A).app ((restriction ρ J A).obj F))
  naturality F F' φ := by
    dsimp [twistedZeroFunctor]
    rw [Category.assoc, ← Functor.map_comp, ← NatTrans.naturality, Functor.id_map,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (restrictionAdjunction ρ J A).unit.naturality φ

theorem twistedCoaugmentation_app (F : Sheaf (twistedTopology ρ J) A) :
    (twistedCoaugmentation ρ J points A).app F =
      (restrictionAdjunction ρ J A).unit.app F ≫
        (induction ρ J A).map
          ((Godement.coaugmentation points A).app ((restriction ρ J A).obj F)) :=
  rfl

/-- With jointly faithful fibers, the twisted coaugmentation is a monomorphism. -/
theorem mono_twistedCoaugmentation_of_jointlyFaithful
    (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := A)))
    (F : Sheaf (twistedTopology ρ J) A) :
    Mono ((twistedCoaugmentation ρ J points A).app F) := by
  have := Godement.mono_coaugmentation_of_jointlyFaithful points A hpoints
    ((restriction ρ J A).obj F)
  change Mono ((restrictionAdjunction ρ J A).unit.app F ≫
    (induction ρ J A).map ((Godement.coaugmentation points A).app ((restriction ρ J A).obj F)))
  infer_instance

variable [Abelian A] [HasSheafify (twistedTopology ρ J) A]

/-- The Godement cochain complex functor of the twisted site, by iterated
cokernels. -/
def twistedComplexFunctor :
    Sheaf (twistedTopology ρ J) A ⥤ CochainComplex (Sheaf (twistedTopology ρ J) A) ℕ :=
  Cohomology.CokernelComplex.functor (twistedZeroFunctor ρ J points A)
    (twistedCoaugmentation ρ J points A)

/-- The Godement complex of a sheaf on the twisted site. -/
abbrev twistedComplex (F : Sheaf (twistedTopology ρ J) A) :
    CochainComplex (Sheaf (twistedTopology ρ J) A) ℕ :=
  (twistedComplexFunctor ρ J points A).obj F

/-- The augmentation of the twisted Godement complex. -/
def twistedAugmentation (F : Sheaf (twistedTopology ρ J) A) :
    F ⟶ (twistedComplex ρ J points A F).X 0 :=
  (twistedCoaugmentation ρ J points A).app F

@[reassoc (attr := simp)]
theorem twistedAugmentation_d (F : Sheaf (twistedTopology ρ J) A) :
    twistedAugmentation ρ J points A F ≫ (twistedComplex ρ J points A F).d 0 1 = 0 :=
  Cohomology.CokernelComplex.augmentation_d _ _ F

end Godement

section Discrete

variable [TopologicalSpace G] (L : LocalActionSystem (TwistedOver P ρ) G)
variable {I : Type w} (points : I → GrothendieckTopology.Point.{w} J)
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

/-- The degree-zero Godement functor on discrete sheaves: the discrete part of the
twisted Godement functor. -/
def discreteZeroFunctor :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    twistedZeroFunctor ρ J points (ModuleCat.{w} R) ⋙ discreteCoreflector L (twistedTopology ρ J)

/-- The coaugmentation on discrete sheaves. -/
def discreteCoaugmentation : 𝟭 _ ⟶ discreteZeroFunctor ρ J L points R where
  app F := (discreteAdjunction L (twistedTopology ρ J)).unit.app F ≫
    (discreteCoreflector L (twistedTopology ρ J)).map
      ((twistedCoaugmentation ρ J points (ModuleCat.{w} R)).app
        ((L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).obj F))
  naturality F F' φ := by
    dsimp [discreteZeroFunctor]
    rw [Category.assoc, ← Functor.map_comp, ← NatTrans.naturality, Functor.id_map,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1

/-- With jointly faithful fibers, the coaugmentation on discrete sheaves is a
monomorphism. -/
theorem mono_discreteCoaugmentation_of_jointlyFaithful
    (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) :
    Mono ((discreteCoaugmentation ρ J L points R).app F) := by
  have := mono_twistedCoaugmentation_of_jointlyFaithful ρ J points (ModuleCat.{w} R) hpoints
    ((L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).obj F)
  have : (discreteCoreflector (R := R) L (twistedTopology ρ J)).IsRightAdjoint :=
    (discreteAdjunction (R := R) L (twistedTopology ρ J)).isRightAdjoint
  have : IsIso ((discreteAdjunction (R := R) L (twistedTopology ρ J)).unit.app F) :=
    inferInstance
  change Mono ((discreteAdjunction L (twistedTopology ρ J)).unit.app F ≫
    (discreteCoreflector L (twistedTopology ρ J)).map
      ((twistedCoaugmentation ρ J points (ModuleCat.{w} R)).app
        ((L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J)).obj F)))
  infer_instance

variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- The Godement cochain complex functor on discrete sheaves. -/
def discreteComplexFunctor :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      CochainComplex (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℕ :=
  Cohomology.CokernelComplex.functor (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R)

end Discrete

end Langlands.Sheaf.Equivariant.TwistedOver
