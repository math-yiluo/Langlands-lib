import Langlands.Sheaf.Equivariant.TwistedGodement

/-!
# Godement constructions on a coreflective subcategory of twisted sheaves

Let `G` act on `X`, let `J` be a translation-invariant topology on `P.Over ⊤ X` with a
family of points, and let `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)` be a fully
faithful functor with a right adjoint `cor`. The published module `TwistedGodement` defines
the degree-zero Godement functor of the twisted site and, for the discrete sheaves of a
local action system, its discrete part. This module does the same for `𝒜`: the Godement
functor `incl ⋙ C⁰ ⋙ cor`, its coaugmentation, which is monic when the fibers at the points
are jointly faithful, and, for abelian `𝒜`, the Godement complex by iterated cokernels.
The locally discrete sheaves of `LocalActionSmoothPart`, which model Berkovich's étale
`G`-sheaves, are an instance.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable {I : Type w} (points : I → GrothendieckTopology.Point.{w} J)
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
variable (cor : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ 𝒜)

/-- The degree-zero Godement functor on `𝒜`: include into sheaves on the twisted site,
apply the twisted Godement functor, and take the right adjoint `cor`. -/
def exactZeroFunctor : 𝒜 ⥤ 𝒜 :=
  incl ⋙ twistedZeroFunctor ρ J points (ModuleCat.{w} R) ⋙ cor

variable {incl cor} (adj : incl ⊣ cor)

/-- The coaugmentation on `𝒜`: the unit of `adj` followed by `cor` applied to the twisted
coaugmentation. -/
def exactCoaugmentation : 𝟭 𝒜 ⟶ exactZeroFunctor ρ J points R incl cor where
  app F := adj.unit.app F ≫
    cor.map ((twistedCoaugmentation ρ J points (ModuleCat.{w} R)).app (incl.obj F))
  naturality F F' φ := by
    dsimp [exactZeroFunctor]
    rw [Category.assoc, ← Functor.map_comp, ← NatTrans.naturality, Functor.id_map,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact adj.unit.naturality φ

theorem exactCoaugmentation_app (F : 𝒜) :
    (exactCoaugmentation ρ J points R adj).app F =
      adj.unit.app F ≫
        cor.map ((twistedCoaugmentation ρ J points (ModuleCat.{w} R)).app (incl.obj F)) :=
  rfl

/-- If `incl` is fully faithful and the fibers at the points are jointly faithful, the
coaugmentation on `𝒜` is a monomorphism: the unit of `adj` is an isomorphism, the twisted
coaugmentation is a monomorphism and the right adjoint `cor` preserves monomorphisms. -/
theorem mono_exactCoaugmentation_of_jointlyFaithful [incl.Full] [incl.Faithful]
    (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))
    (F : 𝒜) : Mono ((exactCoaugmentation ρ J points R adj).app F) := by
  have := mono_twistedCoaugmentation_of_jointlyFaithful ρ J points (ModuleCat.{w} R) hpoints
    (incl.obj F)
  have : cor.IsRightAdjoint := adj.isRightAdjoint
  rw [exactCoaugmentation_app]
  refine @mono_comp _ _ _ _ _ _ ?_ _ ?_
  · infer_instance
  · exact cor.map_mono _

/-- The Godement cochain complex functor on an abelian `𝒜`, by iterated cokernels. -/
def exactComplexFunctor [Abelian 𝒜] : 𝒜 ⥤ CochainComplex 𝒜 ℕ :=
  Cohomology.CokernelComplex.functor (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj)

end Langlands.Sheaf.Equivariant.TwistedOver
