import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Langlands.Sheaf.Equivariant.LocalActionFiniteFixedSections

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z uA vA wA uI uR w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))}

/-- The full local action of a supplied lift on an admissible object is an
admissible action for the lift system. -/
theorem isAdmissible_liftAction (Adm : P.Over ⊤ X → Prop) {U : P.Over ⊤ X}
    (l : ActionLift ρ U.hom) (hU : Adm U) :
    (liftSystem P ρ Adm).IsAdmissible ((ι P ρ).obj U) (liftOpenSubgroup l)
      (liftAction l) := by
  refine ⟨hU, l, le_rfl, ?_⟩
  ext h
  rfl

section Concrete

variable {A : Type uA} [Category.{vA} A] {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- One common open subgroup fixing sections over finitely many admissible
analytic objects with supplied action lifts. -/
def finiteLiftFixedSections (Adm : P.Over ⊤ X → Prop)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ A) (hF : (liftSystem P ρ Adm).IsDiscrete F)
    {I : Type uI} [Finite I] (U : I → P.Over ⊤ X)
    (l : ∀ i, ActionLift ρ (U i).hom) (hU : ∀ i, Adm (U i))
    (s : ∀ i, ToType (F.obj (op ((ι P ρ).obj (U i))))) (Q : OpenSubgroup G) :
    CommonFixedSections F (fun i => (ι P ρ).obj (U i))
      (fun i => liftOpenSubgroup (l i)) (fun i => liftAction (l i)) s Q :=
  (liftSystem P ρ Adm).commonFixedSections F hF
    (fun i => (ι P ρ).obj (U i)) (fun i => liftOpenSubgroup (l i))
    (fun i => liftAction (l i)) (fun i => isAdmissible_liftAction Adm (l i) (hU i)) s Q

end Concrete

section Modules

variable {R : Type uR} [CommRing R]

/-- For finitely many supplied admissible analytic lifts, the directed union
of simultaneous fixed-family submodules is the whole product of sections. -/
theorem iSup_liftFixedFamilySubmodule (Adm : P.Over ⊤ X → Prop)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : (liftSystem P ρ Adm).IsDiscrete F)
    {I : Type uI} [Finite I] (U : I → P.Over ⊤ X)
    (l : ∀ i, ActionLift ρ (U i).hom) (hU : ∀ i, Adm (U i)) (Q : OpenSubgroup G) :
    (⨆ N : CommonOpenSubgroup Q (fun i => liftOpenSubgroup (l i)),
      fixedFamilySubmodule F (fun i => liftAction (l i)) N.val) = ⊤ :=
  LocalActionSystem.iSup_fixedFamilySubmodule F (fun i => liftAction (l i))
    (liftSystem P ρ Adm) hF (fun i => isAdmissible_liftAction Adm (l i) (hU i)) Q

end Modules

end Langlands.Sheaf.Equivariant.Analytic
