/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomPullbackMateSections
import WeilConjectures.AlgebraicGeometry.InternalHomCounitMateIso

/-! # Derived internal Hom adjunction for pullback and direct image

Source: Stacks Project, Cohomology, Remark 08I3 and Lemmas 079W, 08DJ
(blueprint: lem-pc-derived-internal-hom-pullback-adjunction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical internal-Hom comparison, its counit composite as a natural isomorphism,
and its map on zeroth hypercohomology. The witnesses are the adjunction `a`
(Lg^* ⊣ Rg_*), the tensor/internal-Hom adjunctions `bS`, `bT`, and the pullback--tensor
comparison `t` (lem-pc-derived-pullback-tensor-product), in the form of the existing
lem-pc-sheaf-rhom-projection-formula. The first equation specifies gamma as the mate under
`a` and `bT` of `t.inv` followed by Lg^* of evaluation (the counit of `bS`, the transpose of
the identity of internal Hom). The isomorphism `d` is the counit composite, `z` is the
comparison of global sections with pushforward (lem-pc-derived-sections-pushforward-comparison),
and `eS`, `eT` are identifications H⁰(RHom(L,M)) = Hom(L,M) natural in both variables, as
in lem-pur-rhom-global-sections; the final equation says the map induced on H⁰ is
φ ↦ ε_E ∘ Lg^*φ.

Source: Stacks Project, Cohomology, Remark 08I3, Tags 079W and 08DJ
(blueprint: lem-pc-derived-internal-hom-pullback-adjunction).

Proof:
1. Obtain `a` from lem-pc-ringed-spaces-derived-adjoint-general, `bS` and `bT` from
   lem-sc-derived-internal-hom-adjunction, and `t` from
   lem-pc-derived-pullback-tensor-product. Pull back evaluation, precompose with `t.inv`,
   transpose by `bT`, then take the mate by `a`; this constructs gamma. Naturality of
   all the adjunctions and of `t` makes gamma a natural transformation.
2. Compose gamma with direct image of internal Hom applied to the counit of `a`.
   Test against any object A on S: tensor/internal-Hom adjunction on S followed by
   `a` and `t` identifies maps into the source with maps from Lg*A tensor Lg*M into E.
   The adjunction `a` followed by tensor/internal-Hom adjunction on T identifies maps
   into the target with that same group. The triangle identities, naturality and the
   defining evaluation equation make postcomposition the identity under these
   bijections. Yoneda gives invertibility. All constructions are natural in M and E.
3. Apply H⁰. Use lem-pur-rhom-global-sections on both schemes and
   lem-pc-derived-sections-pushforward-comparison on the whole scheme for `z`.
   Taking the mate and postcomposing with the counit sends a morphism phi to
   Lg*(phi) followed by the counit, as the last equation records. -/
theorem derivedInternalHom_pullback_adjunction
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (bS : ∀ K : schemeDerivedCategory S, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj
            (op K))
      (bT : ∀ K : schemeDerivedCategory T, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)).obj
            (op K))
      (t : tensor (schemeDerivedCategory S) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory T))
      (γ : derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf ⟶
        (derivedPullback g).op.prod (derivedPullback g) ⋙
          derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage g)
      (d : (𝟭 (schemeDerivedCategory S)).op.prod (schemeDerivedDirectImage g) ⋙
          derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf ≅
        (derivedPullback g).op.prod (𝟭 (schemeDerivedCategory T)) ⋙
          derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage g)
      (z : schemeDerivedDirectImage g ⋙
          ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf ≅
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)
      (eS : ∀ P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P)),
        eS P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P)),
        eT P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ K L : schemeDerivedCategory S,
        (a.homEquiv
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))
            ((derivedInternalHom (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
                (op ((derivedPullback g).obj K), (derivedPullback g).obj L))).symm
            (γ.app (op K, L)) =
          (bT ((derivedPullback g).obj K)).homEquiv
            ((derivedPullback g).obj
              ((derivedInternalHom (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).obj (op K, L))) ((derivedPullback g).obj L)
            (t.inv.app
                ((derivedInternalHom (Opens.grothendieckTopology S)
                  S.toRingedSpace.sheaf).obj (op K, L), K) ≫
              (derivedPullback g).map ((bS K).counit.app L))) ∧
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T),
        d.hom.app (op M, E) =
          γ.app (op M, (schemeDerivedDirectImage g).obj E) ≫
            (schemeDerivedDirectImage g).map
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).map
                (X := (op ((derivedPullback g).obj M),
                  (derivedPullback g).obj ((schemeDerivedDirectImage g).obj E)))
                (Y := (op ((derivedPullback g).obj M), E))
                ((𝟙 ((derivedPullback g).obj M)).op, a.counit.app E))) ∧
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op M, (schemeDerivedDirectImage g).obj E))),
        eT (op ((derivedPullback g).obj M), E)
          ((z.hom.app
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).obj (op ((derivedPullback g).obj M), E)))
            ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).map (d.hom.app (op M, E)) x)) =
          (derivedPullback g).map
              (eS (op M, (schemeDerivedDirectImage g).obj E) x) ≫
            a.counit.app E) := by
  have h := exists_derivedInternalHom_pullback_mate_sections.{u, w} g
  rcases h with ⟨a, bS, bT, t, γ, z, eS, eT, heS, heT, hγ, hsections⟩
  let F := derivedPullback g
  let R := schemeDerivedDirectImage g
  let H := derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf
  let J := derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf
  let c : (𝟭 (schemeDerivedCategory S)).op.prod R ⋙ H ⟶
      F.op.prod (𝟭 (schemeDerivedCategory T)) ⋙ J ⋙ R :=
    Functor.whiskerLeft ((𝟭 (schemeDerivedCategory S)).op.prod R) γ ≫
      Functor.whiskerRight
        (Functor.whiskerRight (NatTrans.prod (𝟙 F.op) a.counit) J) R
  have hc (P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory T) :
      IsIso (c.app P) := by
    exact internalHomCounitMate_isIso H J F R a bS bT t γ hγ P.1.unop P.2
  let d := NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (c.app P) (hc P))
    (fun f ↦ c.naturality f)
  refine ⟨a, bS, bT, t, γ, d, z, eS, eT, heS, heT, hγ, ?_, ?_⟩
  · intro M E
    rfl
  · intro M E x
    exact hsections M E x

end AlgebraicGeometry
