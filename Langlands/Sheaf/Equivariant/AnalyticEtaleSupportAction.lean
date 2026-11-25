import Langlands.Sheaf.Equivariant.AnalyticEtaleSupportDescent
import Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalGerms

/-! # Underlying support and equality of translated global sections -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {R : Type (max u (v + 1) uL)} [CommRing R]

/-- A global germ vanishes outside the underlying support of the section. -/
theorem etaleGlobalGermMap_eq_zero_of_not_mem_underlyingSupport
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) (x : (localizedFieldPointFunctor L).obj X)
    (hx : pointProjection L X x ∉ etaleUnderlyingSupport L h F.obj s) :
    etaleGlobalGermMap L h F s x = 0 := by
  by_contra hne
  exact hx ⟨x, ⟨etaleSelfPoint L h x, hne⟩, rfl⟩

/-- Equality of global germs over a set containing both underlying supports
detects equality of sections when the point projection is surjective. -/
theorem eq_of_etaleGlobalGermMap_eq_on_underlyingSupport
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s t : F.obj.obj (op (etaleSelf X)))
    (W : Set (localizedSpaceFunctor.obj X))
    (hs : etaleUnderlyingSupport L h F.obj s ⊆ W)
    (ht : etaleUnderlyingSupport L h F.obj t ⊆ W)
    (hst : ∀ x, pointProjection L X x ∈ W →
      etaleGlobalGermMap L h F s x = etaleGlobalGermMap L h F t x) :
    s = t := by
  apply etaleGlobalGermMap_injective L h hX F
  funext x
  by_cases hx : pointProjection L X x ∈ W
  · exact hst x hx
  · rw [etaleGlobalGermMap_eq_zero_of_not_mem_underlyingSupport L h F s x
      (fun hx' => hx (hs hx')),
      etaleGlobalGermMap_eq_zero_of_not_mem_underlyingSupport L h F t x
        (fun hx' => hx (ht hx'))]

/-- Global sections supported in `W` embed into their family of germs over `W`,
provided every underlying point has an `L`-valued lift. -/
def etaleSupportedGlobalGermEmbedding
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (W : Set (localizedSpaceFunctor.obj X)) :
    {s : F.obj.obj (op (etaleSelf X)) // etaleUnderlyingSupport L h F.obj s ⊆ W} ↪
      ∀ x : {x : (localizedFieldPointFunctor L).obj X // pointProjection L X x ∈ W},
        ((etalePoints L h x.val).presheafFiber
          (A := ModuleCat.{max u (v + 1) uL} R)).obj F.obj where
  toFun s x := etaleGlobalGermMap L h F s.val x.val
  inj' := by
    intro s t hst
    apply Subtype.ext
    apply eq_of_etaleGlobalGermMap_eq_on_underlyingSupport L h hX F s.val t.val W
      s.property t.property
    intro x hx
    exact congrFun hst ⟨x, hx⟩

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- The underlying support of a translated section is the image of the
original underlying support under the actual analytic automorphism. -/
theorem etaleUnderlyingSupport_actionRepresentation
    (F : (TwistedOver (etale (K := K)) ρ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (g : G) (s : F.obj (op (base etale ρ))) :
    etaleUnderlyingSupport L h ((ι etale ρ).op ⋙ F)
        (actionRepresentation F (baseAction etale ρ) g s) =
      localizedSpaceFunctor.map (ρ g).asIso.hom ''
        etaleUnderlyingSupport L h ((ι etale ρ).op ⋙ F) s := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  let := EtaleSite.pointAction L ρ
  refine (congrArg (fun S => pointProjection L X '' S)
    (support_actionRepresentation (EtaleSite.pointEquivariance L ρ h) F g s)).trans ?_
  ext y
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨pointProjection L X x', ⟨x', hx', rfl⟩,
      (pointProjection_map L (ρ g).asIso.hom x').symm⟩
  · rintro ⟨y', ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, pointProjection_map L (ρ g).asIso.hom x⟩

/-- If a set contains the support and its translate and the germs agree
there, the global section is fixed by the given group element. -/
theorem actionRepresentation_eq_of_etaleGlobalGermMap_eq_on
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R))
    (g : G) (s : F.obj.obj (op (base etale ρ)))
    (W : Set (localizedSpaceFunctor.obj X))
    (hs : etaleUnderlyingSupport L h ((ι etale ρ).op ⋙ F.obj) s ⊆ W)
    (hW : ∀ y ∈ W, localizedSpaceFunctor.map (ρ g).asIso.hom y ∈ W)
    (hgerm : ∀ x, pointProjection L X x ∈ W →
      etaleGlobalGermMap L h
          ((TwistedOver.restriction ρ (etaleTopology X)
            (ModuleCat.{max u (v + 1) uL} R)).obj F)
          (actionRepresentation F.obj (baseAction etale ρ) g s) x =
        etaleGlobalGermMap L h
          ((TwistedOver.restriction ρ (etaleTopology X)
            (ModuleCat.{max u (v + 1) uL} R)).obj F) s x) :
    actionRepresentation F.obj (baseAction etale ρ) g s = s := by
  apply eq_of_etaleGlobalGermMap_eq_on_underlyingSupport L h hX
    ((TwistedOver.restriction ρ (etaleTopology X)
      (ModuleCat.{max u (v + 1) uL} R)).obj F)
    _ s W _ hs hgerm
  exact (etaleUnderlyingSupport_actionRepresentation L h ρ F.obj g s).trans_subset (by
    rintro y ⟨y', hy', rfl⟩
    exact hW y' (hs hy'))

end Langlands.Sheaf.Equivariant.Analytic
