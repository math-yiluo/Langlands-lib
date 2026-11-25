/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInjective
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage

/-!
# Global sections under the abelian Galois stalk equivalence

Source: Stacks Project, Etale Cohomology, Tag 04JM, lemma-global-sections-point.
(blueprint: lem-sc-etale-global-sections-galois-invariants).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Global sections identify naturally with the invariants of the canonical stalk
representation. Only degree zero is asserted; no derived or continuous cohomology
comparison is assumed.

Source: Stacks Project, Etale Cohomology, Tag 04JM, lemma-global-sections-point,
and Tag 04JQ, lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-sc-etale-global-sections-galois-invariants).

Proof: The set-valued stalk equivalence identifies sections over Spec K with the
fixed elements of the stalk (04JM). Explicitly, restrict to finite separable
extensions in Ks. A germ has a representative on such a field: shrink its
pointed etale neighbourhood to the finite connected component containing its
geometric point. Enlarge to a finite Galois extension. Germ maps from these
connected objects are injective, since a further pointed neighbourhood is an
etale surjective cover and the sheaf equalizer gives injective restriction.
If a germ is invariant, this injectivity makes its representative invariant
under the finite Galois group. Galois descent therefore produces a unique
section over K. Conversely, a section over K has unchanged pullbacks under
every change of geometric lift. The action hypothesis `hi` and the stalk
isomorphism `i` identify this lift-change action with the representation action.
The germ map preserves addition, and its inverse consequently does too.
For a sheaf morphism, its pullback commutes with all restriction and germ maps;
naturality of `i` identifies the resulting map with `E.functor.map`, giving
the displayed naturality equality. Only finite etale neighbourhoods in Ks are
used; Omega may contain transcendental elements over K. -/
theorem etaleGlobalSections_galoisInvariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (hi : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) →
      ∀ (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
      ∀ (z : F.obj.obj (op X)),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z)
    : ∃ t : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
        F.obj.obj (op T) ≃+ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
          (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ),
      ∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (φ : F ⟶ F') (z : F.obj.obj (op T)),
        (t F' (φ.hom.app (op T) z)).val = (E.functor.map φ).hom.hom (t F z).val := by
  classical
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let x : p.fiber.obj T := (p.uniqueFiberObj T hT).default
  have himage := etaleGlobalSections_galoisInvariants_image K Ks Ω T hT E i hi x
  have hinj := etaleGlobalSections_galoisInvariants_injective K Ks Ω T hT E i x
  let f (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      F.obj.obj (op T) →+ (E.functor.obj F).obj.V :=
    (i.inv.app F).hom.comp (p.toPresheafFiber T x F.obj).hom
  have hmem (F) (z : F.obj.obj (op T)) :
      f F z ∈ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) :=
    (himage F (f F z)).2 ⟨z, rfl⟩
  let q (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      F.obj.obj (op T) →+ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) :=
    { toFun := fun z ↦ ⟨f F z, hmem F z⟩
      map_zero' := Subtype.ext (f F).map_zero
      map_add' := fun a b ↦ Subtype.ext ((f F).map_add a b) }
  have hbij (F) : Function.Bijective (q F) := by
    constructor
    · intro a b h
      exact hinj F (congrArg Subtype.val h)
    · intro v
      obtain ⟨z, hz⟩ := (himage F v.val).1 v.property
      exact ⟨z, Subtype.ext hz⟩
  let t := fun F ↦ AddEquiv.ofBijective (q F) (hbij F)
  refine ⟨t, ?_⟩
  intro F F' φ z
  change f F' (φ.hom.app (op T) z) = (E.functor.map φ).hom.hom (f F z)
  have hg := p.toPresheafFiber_naturality φ.hom T x
  have hn := i.inv.naturality φ
  have hga := ConcreteCategory.congr_hom hg z
  have hna := ConcreteCategory.congr_hom hn (p.toPresheafFiber T x F.obj z)
  change (i.inv.app F') (p.toPresheafFiber T x F'.obj (φ.hom.app (op T) z)) = _
  change p.presheafFiber.map φ.hom (p.toPresheafFiber T x F.obj z) =
    p.toPresheafFiber T x F'.obj (φ.hom.app (op T) z) at hga
  change (i.inv.app F') (p.presheafFiber.map φ.hom
    (p.toPresheafFiber T x F.obj z)) =
    (E.functor.map φ).hom.hom ((i.inv.app F) (p.toPresheafFiber T x F.obj z)) at hna
  exact (congrArg (i.inv.app F') hga.symm).trans hna

end AlgebraicGeometry.Scheme
