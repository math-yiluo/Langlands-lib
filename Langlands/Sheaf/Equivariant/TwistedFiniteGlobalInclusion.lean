import Langlands.Sheaf.Equivariant.TwistedFiniteGlobalSections
import Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison

/-!
# The global-section inclusion under finite base subcovers

Finite-cover descent makes the full representation of global sections smooth.
Consequently the canonical inclusion of its smooth part is an isomorphism,
functorially on every category of locally discrete module sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory Opposite

universe w v u uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type w} [CommRing R]

/-- Finite base subcovers make the global representation of a locally discrete
module sheaf smooth. -/
theorem isSmooth_baseSections_of_locallyDiscrete
    {J : GrothendieckTopology (TwistedOver P ρ)} (hfin : HasFiniteBaseSubcovers J)
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F)
    (hloc : L.IsLocallyDiscrete J F) :
    Langlands.IsSmooth (actionRepresentation F (baseAction P ρ)) := by
  intro s
  obtain ⟨K, -, hK⟩ := isDiscreteSection_base_of_locallyDiscrete hfin L hL hF hloc s
  refine ⟨K, ?_⟩
  intro k
  exact hK ⟨k, Subgroup.mem_top _⟩ k.property

variable [P.RespectsIso]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R)

/-- Under finite base subcovers, a locally discrete sheaf has all its global
sections in the smooth part, so the canonical smooth-global inclusion is an
isomorphism. -/
theorem isIso_sheafSmoothGlobalInclusion_app_of_locallyDiscrete
    (hfin : HasFiniteBaseSubcovers (twistedTopology ρ J))
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
    (hloc : L.IsLocallyDiscrete (twistedTopology ρ J) F.obj) :
    IsIso ((sheafSmoothGlobalInclusion J R).app F) := by
  have hsm := isSmooth_baseSections_of_locallyDiscrete hfin L hL F.property hloc
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨Subtype.val_injective, fun s => ⟨⟨s, hsm s⟩, rfl⟩⟩

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))

/-- The canonical global-section inclusion is a natural isomorphism whenever
the image sheaves are locally discrete and the base has finite subcovers. -/
theorem isIso_exactGlobalInclusion_of_locallyDiscrete
    (hfin : HasFiniteBaseSubcovers (twistedTopology ρ J))
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    (hloc : ∀ A : 𝒜, L.IsLocallyDiscrete (twistedTopology ρ J) (incl.obj A).obj) :
    IsIso (exactGlobalInclusion J R incl) := by
  have : ∀ A : 𝒜, IsIso ((exactGlobalInclusion J R incl).app A) := fun A =>
    isIso_sheafSmoothGlobalInclusion_app_of_locallyDiscrete (J := J) (R := R) hfin L hL
      (incl.obj A) (hloc A)
  exact NatIso.isIso_of_isIso_app _

/-- Smooth global sections coincide naturally with the full global sections
of the restriction under finite base subcovers and local discreteness. -/
def finiteGlobalSectionsIso
    (hfin : HasFiniteBaseSubcovers (twistedTopology ρ J))
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    (hloc : ∀ A : 𝒜, L.IsLocallyDiscrete (twistedTopology ρ J) (incl.obj A).obj) :
    exactGlobalSections J R incl ⋙ smoothForget R G ≅
      exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj :=
  haveI := isIso_exactGlobalInclusion_of_locallyDiscrete (J := J) (R := R) incl hfin L hL hloc
  asIso (exactGlobalInclusion J R incl)

end Langlands.Sheaf.Equivariant.TwistedOver
