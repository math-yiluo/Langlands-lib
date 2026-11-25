/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.OpenExtensionProjectionFormula

/-! # Invertibility of the mixed-universe open-restriction evaluation mate
Source: Stacks Project, Tags 08DJ, 08DL and 08BS.
(blueprint: lem-pc-open-restriction-evaluation-mate-is-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Use the standard localization on the open scheme.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-open-restriction-evaluation-mate-is-iso). -/
local instance openRestrictionMateStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem mate_isIso_of_projection
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (HU : Dᵒᵖ × D ⥤ D) (R : C ⥤ D) [R.Monoidal]
    (J : D ⥤ C) (adj : J ⊣ R)
    (e : ∀ A K N : C, (A ⟶ H.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (eU : ∀ A K N : D, (A ⟶ HU.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (hx : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ H.obj (op K, N)),
      e A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ e A K N f)
    (hu : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ HU.obj (op K, N)),
      eU A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ eU A K N f)
    (K N : C)
    (p : ∀ A : D, J.obj (A ⊗ R.obj K) ≅ J.obj A ⊗ K)
    (hp : ∀ A : D, adj.unit.app (A ⊗ R.obj K) ≫ R.map (p A).hom =
      (adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫ (Functor.Monoidal.μIso R (J.obj A) K).hom) :
    IsIso ((eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
      ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
        R.map (e (H.obj (op K, N)) K N (𝟙 _)))) := by
  let c := (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
    ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
      R.map (e (H.obj (op K, N)) K N (𝟙 _)))
  apply isIso_of_yoneda_map_bijective c
  intro A
  let pe : (J.obj A ⊗ K ⟶ N) ≃ (J.obj (A ⊗ R.obj K) ⟶ N) :=
    { toFun := fun f ↦ (p A).hom ≫ f
      invFun := fun f ↦ (p A).inv ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  let b := (adj.homEquiv A (H.obj (op K, N))).symm |>.trans (e (J.obj A) K N)
    |>.trans pe |>.trans (adj.homEquiv (A ⊗ R.obj K) N)
    |>.trans (eU A (R.obj K) (R.obj N)).symm
  have hb (f : A ⟶ R.obj (H.obj (op K, N))) : b f = f ≫ c := by
    apply (eU A (R.obj K) (R.obj N)).injective
    dsimp only [b, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    change (adj.homEquiv (A ⊗ R.obj K) N)
      ((p A).hom ≫ e (J.obj A) K N ((adj.homEquiv A _).symm f)) =
      eU A (R.obj K) (R.obj N) (f ≫ c)
    rw [adj.homEquiv_unit, R.map_comp, ← Category.assoc, hp]
    have hx' := hx (H.obj (op K, N)) (J.obj A) K N
      ((adj.homEquiv A _).symm f) (𝟙 _)
    simp only [Category.comp_id] at hx'
    rw [hx', R.map_comp, Category.assoc]
    have hn := Functor.LaxMonoidal.μ_natural R ((adj.homEquiv A _).symm f) (𝟙 K)
    rw [R.map_id] at hn
    change (R.map ((adj.homEquiv A _).symm f) ⊗ₘ 𝟙 (R.obj K)) ≫
      (Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom =
      (Functor.Monoidal.μIso R (J.obj A) K).hom ≫
        R.map ((adj.homEquiv A _).symm f ⊗ₘ 𝟙 K) at hn
    rw [← reassoc_of% hn, ← Category.assoc, tensorHom_comp_tensorHom]
    have hf : adj.unit.app A ≫ R.map ((adj.homEquiv A _).symm f) = f := by
      have h := (adj.homEquiv A (H.obj (op K, N))).apply_symm_apply f
      rw [adj.homEquiv_unit] at h
      exact h
    rw [hf, Category.id_comp, hu]
    simp only [c, Equiv.apply_symm_apply]
  have heq : (fun f : A ⟶ R.obj (H.obj (op K, N)) ↦ f ≫ c) = b := by
    funext f
    exact (hb f).symm
  change Function.Bijective (fun f : A ⟶ R.obj (H.obj (op K, N)) ↦ f ≫ c)
  rw [heq]
  exact b.bijective

set_option linter.style.haveILetI false in
/-- The mate of restricted evaluation is invertible for any strong monoidal
structure on the exact restriction functor, with independently specified localizations.

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL;
Tag 08BS and modules.tex, Tag 01AK, for exact extension by zero.
(blueprint: lem-pc-open-restriction-evaluation-mate-is-iso).

Proof: let J be exact derived extension by zero, transported from the over-site
along its equivalence with modules on U.toScheme. Localization of the ordinary
adjunction gives J left adjoint to R, with invertible unit. Its essential image
consists of complexes whose cohomology stalks outside U vanish. Restriction
reflects isomorphisms between such objects, since all other stalks vanish.
For any A on U and K on X, J(A) tensor K is supported on U: compute the tensor
on K-flat representatives and use the acyclic outside stalks. The adjoint of
(unit_A tensor identity); μ_R(J(A),K) is an isomorphism
J(A tensor R(K)) -> J(A) tensor K. Indeed both objects are supported on U,
and its restriction is identified by the adjunction identities with a composite
of the invertible unit and the invertible tensorator. Thus it is invertible.
For any test object A, use the adjunction, the canonical tensor-Hom bijection
on X, this projection isomorphism, and the adjunction on the tensor target.
Their composite is a bijection from Hom(A,R(H(K,N))) to
Hom(A tensor R(K),R(N)). Naturality of the tensorator and tensor-Hom bijection
identifies it with f mapped to (f tensor identity); μ_R(H(K,N),K);
R(e_X(identity)). Currying on U identifies this bijection with
postcomposition by the displayed mate. This is bijective for every A, so
Yoneda makes the mate invertible. The proof only uses naturality and
invertibility of the tensorators, so it works for every monoidal structure m.
All adjunctions and factorization isomorphisms are induced through the specified
localizations independently; no common morphism universe is assumed.
For the empty open all test objects are zero and the same bijections hold;
zero K or N gives an isomorphism between zero internal-Hom objects. -/
theorem openRestriction_evaluationMate_isIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    ∀ m : R.Monoidal,
      letI := m
      ∀ K N : schemeDerivedCategory X,
        IsIso ((schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
            ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
              R.map (schemeDerivedTensorHomEquiv X (H.obj (op K, N)) K N (𝟙 _)))) := by
  classical
  dsimp only
  let E := (Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
  let HU := derivedInternalHom
    (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
  let e := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  have he : IsCanonicalDerivedTensorHom X e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom X)
  have heU : IsCanonicalDerivedTensorHom U.toScheme eU :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)
  intro m K N
  letI : R.Monoidal := m
  -- Eliminate the witnesses without normalizing the concrete derived functors.
  refine (exists_openExtension_projectionFormula X U m).elim fun J hJ ↦ ?_
  refine hJ.elim fun adj hp ↦ ?_
  have hi (A : schemeDerivedCategory U.toScheme) :
      IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
        ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
          (Functor.Monoidal.μIso R (J.obj A) K).hom)) := hp A K
  let p := fun A ↦ asIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
    ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
      (Functor.Monoidal.μIso R (J.obj A) K).hom))
  apply mate_isIso_of_projection H HU R J adj e eU ?_ ?_ K N p ?_
  · intro B B' L M a f
    have hn := he.1 B B' L L M M a (𝟙 L) (𝟙 M) f
    change e B' L M (a ≫ f ≫ H.map (𝟙 (op L, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn
  · intro B B' L M a f
    have hn := heU.1 B B' L L M M a (𝟙 L) (𝟙 M) f
    change eU B' L M (a ≫ f ≫ HU.map (𝟙 (op L, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn
  · intro A
    have h := (adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).apply_symm_apply
      ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
        (Functor.Monoidal.μIso R (J.obj A) K).hom)
    rw [adj.homEquiv_unit] at h
    exact h

end AlgebraicGeometry
