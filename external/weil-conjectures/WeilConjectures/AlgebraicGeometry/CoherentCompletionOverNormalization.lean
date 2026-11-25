/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Normalized completion on an open over-site

Source: Stacks Project, Tag 0889(1), Zariski locality, and equation 0880.
(blueprint: lem-weil-pbc-coherent-completion-over-normalization).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a coherent module to an open over-site preserves coherence and has
an inverse-system quotient comparison normalized by the original projections.

Source: Stacks Project, Tag 0889(1), first sentence of proof; equation 0880.
(blueprint: lem-weil-pbc-coherent-completion-over-normalization).

Proof: Identify the over-site with the open subscheme using overFunctorEquiv.
Coherence restricts to that subscheme. Restriction preserves cokernels and the
images of multiplication by every ideal power. Hence the restricted quotient and
quotient of the restriction have the same cokernel universal property. Construct
both comparison maps from this universal property; cancellation of the quotient
projections proves they are inverse. Normalize the comparison by requiring its
composite with the restricted projection to equal the quotient projection of the
restriction. For every transition, precompose with the projection from the larger
quotient's module and cancel that epimorphism. This gives a natural isomorphism of
systems. Transfer it through overFunctorEquiv to the indicated over-site objects.
The construction works for the zero and unit ideals and the empty open: it uses
only cokernel universal properties, with no nonemptiness or affineness assumption.
-/
theorem coherentCompletion_over_normalization
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (W : X.Opens) :
    RingedSpace.IsCoherent W.toScheme.toRingedSpace
      ((Scheme.Modules.overEquiv W).functor.obj (H.obj.over W)) ∧
    ∃ c : (formalCompletionSystem J H.obj ⋙
        SheafOfModules.overFunctor (moduleRings X.toRingedSpace) W ⋙
        (Scheme.Modules.overEquiv W).functor) ≅
      formalCompletionSystem (J.comap W.ι)
        ((Scheme.Modules.overEquiv W).functor.obj (H.obj.over W)),
      ∀ n : ℕᵒᵖ,
        (Scheme.Modules.overEquiv W).functor.map
            ((formalModuleQuotientπ J (n.unop + 1) H.obj).over W) ≫ c.hom.app n =
          formalModuleQuotientπ (J.comap W.ι) (n.unop + 1)
            ((Scheme.Modules.overEquiv W).functor.obj (H.obj.over W)) := by
  classical
  let E := (Scheme.Modules.overEquiv W).functor
  let R := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) W
  let T := Scheme.Modules.restrictFunctor W.ι
  generalize hη : Scheme.Modules.overFunctorEquiv W = η
  let e := η.app H.obj
  have hH : RingedSpace.IsCoherent W.toScheme.toRingedSpace (T.obj H.obj) :=
    (coherent_module_local_on_open_cover X H.obj PUnit (fun _ ↦ ⊤)
      (by simp)).1 H.property W
  have hE : RingedSpace.IsCoherent W.toScheme.toRingedSpace (E.obj (R.obj H.obj)) := by
    have hh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      W.toScheme (T.obj H.obj)).mp hH
    apply (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      W.toScheme _).mpr
    have ht : SheafOfModules.IsFiniteType.{u} (E.obj (R.obj H.obj)) := by
      obtain ⟨p, hp⟩ := hh.2.exists_localGeneratorsData
      have : p.IsFiniteType := hp
      let p' : (E.obj (R.obj H.obj)).LocalGeneratorsData :=
        { I := p.I
          X := p.X
          coversTop := p.coversTop
          generators i := (p.generators i).ofEpi (e.inv.over (p.X i)) }
      have hp' : p'.IsFiniteType := by
        constructor
        intro i
        have := hp.isFiniteType i
        dsimp [p']
        infer_instance
      constructor
      exact ⟨p', hp'⟩
    exact ⟨(SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      e.symm hh.1, ht⟩
  let Hlocal : CoherentModules W.toScheme := ⟨T.obj H.obj, hH⟩
  have bound (n : ℕ) :
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι 0).2
        (kernel (𝟙 (((completion X J).obj H).obj.obj (op n))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι 0).2
        (cokernel (𝟙 (((completion X J).obj H).obj.obj (op n))))) := by
    have monoProduct (M : X.Modules) : Mono (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι 0).2 M) := by
      dsimp [Scheme.idealModuleProductι]
      infer_instance
    constructor
    · exact IsZero.of_mono (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι 0).2 _)
        (isZero_kernel_of_mono (𝟙 _))
    · exact IsZero.of_mono (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι 0).2 _)
        (isZero_cokernel_of_epi (𝟙 _))
  obtain ⟨γ, hγ, _⟩ := torsionControlled_formal_restriction J H
    ((completion X J).obj H) (𝟙 _) W Hlocal rfl 0 bound
  let t := Functor.isoWhiskerLeft (formalCompletionSystem J H.obj)
    η
  let c := t ≪≫ γ ≪≫ (formalCompletionFunctor (J.comap W.ι)).mapIso e.symm
  refine ⟨hE, c, ?_⟩
  intro n
  change E.map ((formalModuleQuotientπ J (n.unop + 1) H.obj).over W) ≫
    η.hom.app
        (formalModuleQuotient J (n.unop + 1) H.obj) ≫
      γ.hom.app n ≫ formalModuleQuotientMap (J.comap W.ι) e.inv
        (Nat.le_refl (n.unop + 1)) = _
  have hn := η.hom.naturality
    (formalModuleQuotientπ J (n.unop + 1) H.obj)
  change E.map ((formalModuleQuotientπ J (n.unop + 1) H.obj).over W) ≫
      η.hom.app
        (formalModuleQuotient J (n.unop + 1) H.obj) =
    e.hom ≫ T.map (formalModuleQuotientπ J (n.unop + 1) H.obj) at hn
  rw [← Category.assoc, hn]
  have hγ' : T.map (formalModuleQuotientπ J (n.unop + 1) H.obj) ≫ γ.hom.app n =
      formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) (T.obj H.obj) := by
    simpa only [op_unop, eqToHom_refl, Category.id_comp] using hγ n.unop
  rw [Category.assoc e.hom, ← Category.assoc (T.map _), hγ']
  have hπ : formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) (T.obj H.obj) ≫
      formalModuleQuotientMap (J.comap W.ι) e.inv (Nat.le_refl (n.unop + 1)) =
      e.inv ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1)
        (E.obj (R.obj H.obj)) := cokernel.π_desc _ _ _
  rw [hπ, Iso.hom_inv_id_assoc]


end AlgebraicGeometry
