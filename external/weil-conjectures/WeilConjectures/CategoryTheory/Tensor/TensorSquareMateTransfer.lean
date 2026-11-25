/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact

/-!
# Mixed tensor-action squares and projection mates

Source: Stacks, sites-cohomology.tex, Tags 0B56 and 07A7; the agent mixed-action
calculation in the node, steps 1–6 (blueprint: lem-sf-tensor-square-mate-transfer).
The tensor products are arbitrary bifunctors. In particular the mixed actions below
are not monoidal structures on the horizontal functors.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB uC vC uD vD

open CategoryTheory

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The existing right-adjoint projection map with an uncurried tensor interface,
allowing a noninvertible tensor comparison. This is its actual bifunctor construction,
not a choice of a map with a desired property.
Source: Stacks Tag 0B56, equation-projection-formula-map, and node step 1
(blueprint: lem-sf-tensor-square-mate-transfer). -/
noncomputable def tensorSquareProjectionMap
    (P : C ⥤ A) (R : A ⥤ C) (adj : P ⊣ R)
    (TC : C × C ⥤ C) (TA : A × A ⥤ A)
    (mu : TC ⋙ P ⟶ (P.prod P) ⋙ TA) (M : A) (Q : C) :
    TC.obj (R.obj M, Q) ⟶ R.obj (TA.obj (M, P.obj Q)) :=
  ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TA)
    (T_D := Functor.curry.obj TC)
    (Functor.curry.map mu ≫ (Functor.curryObjProdComp P P TA).hom)).app M).app Q

private lemma projection_transpose
    (P : C ⥤ A) (R : A ⥤ C) (adj : P ⊣ R)
    (TC : C × C ⥤ C) (TA : A × A ⥤ A)
    (mu : TC ⋙ P ⟶ (P.prod P) ⋙ TA) (M : A) (Q : C) :
    (adj.homEquiv _ _).symm (tensorSquareProjectionMap P R adj TC TA mu M Q) =
      mu.app (R.obj M, Q) ≫ TA.map (Prod.mkHom (adj.counit.app M) (𝟙 (P.obj Q))) := by
  simpa [tensorSquareProjectionMap] using
    adj.homEquiv_symm_rightAdjointProjectionMap_app_app
      (T_C := Functor.curry.obj TA) (T_D := Functor.curry.obj TC)
      (Functor.curry.map mu ≫ (Functor.curryObjProdComp P P TA).hom) M Q

private noncomputable def projectionNatTrans
    (P : C ⥤ A) (R : A ⥤ C) (adj : P ⊣ R)
    (TC : C × C ⥤ C) (TA : A × A ⥤ A)
    (mu : TC ⋙ P ⟶ (P.prod P) ⋙ TA) :
    (R.prod (𝟭 C)) ⋙ TC ⟶ ((𝟭 A).prod P) ⋙ TA ⋙ R where
  app X := tensorSquareProjectionMap P R adj TC TA mu X.1 X.2
  naturality X Y f := by
    have h := (Functor.uncurry.map (adj.rightAdjointProjectionMap
      (T_C := Functor.curry.obj TA) (T_D := Functor.curry.obj TC)
      (Functor.curry.map mu ≫ (Functor.curryObjProdComp P P TA).hom))).naturality f
    simpa [tensorSquareProjectionMap, ← Functor.map_comp] using h

/-- The first path, `d_i`, followed by `J(pi_r)` and the proper-adjunction mate `g`.
Source: Stacks Tags 0B56 and 07A7; node step 2
(blueprint: lem-sf-tensor-square-mate-transfer). -/
noncomputable def tensorSquareMateFirst
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (Rp : B ⥤ D)
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (Pi : D ⥤ C) (J : C ⥤ D) (K : A ⥤ B)
    (TA : A × A ⥤ A) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (di : (J.prod (𝟭 D)) ⋙ TD ⟶ ((𝟭 C).prod Pi) ⋙ TC ⋙ J)
    (a : J ⋙ Pp ⟶ Pr ⋙ K) (M : A) (N : D) :
    TD.obj (J.obj (Rr.obj M), N) ⟶
      Rp.obj (K.obj (TA.obj (M, Pr.obj (Pi.obj N)))) :=
  di.app (Rr.obj M, N) ≫
    J.map (tensorSquareProjectionMap Pr Rr ar TC TA muR M (Pi.obj N)) ≫
    (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).app
      (TA.obj (M, Pr.obj (Pi.obj N)))

/-- The second path, `(g tensor 1)`, followed by `pi_p` and `R_p(d_k)`.
The final inverse comparison makes the suppressed identification explicit; both paths
land in `R_p K (M tensor P_r P_i N)`.
Source: Stacks Tags 0B56 and 07A7; node steps 3–4
(blueprint: lem-sf-tensor-square-mate-transfer). -/
noncomputable def tensorSquareMateSecond
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (Rp : B ⥤ D)
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (Pi : D ⥤ C) (Pk : B ⥤ A)
    (J : C ⥤ D) (K : A ⥤ B) (theta : Pi ⋙ Pr ≅ Pp ⋙ Pk)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TD : D × D ⥤ D)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (dk : (K.prod (𝟭 B)) ⋙ TB ⟶ ((𝟭 A).prod Pk) ⋙ TA ⋙ K)
    (a : J ⋙ Pp ⟶ Pr ⋙ K) (M : A) (N : D) :
    TD.obj (J.obj (Rr.obj M), N) ⟶
      Rp.obj (K.obj (TA.obj (M, Pr.obj (Pi.obj N)))) :=
  TD.map (Prod.mkHom ((mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).app M) (𝟙 N)) ≫
    tensorSquareProjectionMap Pp Rp ap TD TB muP (K.obj M) N ≫
    Rp.map (dk.app (M, Pp.obj N) ≫
      K.map (TA.map (Prod.mkHom (𝟙 M) (theta.inv.app N))))

/-- The specified common transpose `P_p(d_i)` followed by `a` and `K(c)`, where
`c` is the tensor comparison followed by the first counit tensored with identity.
Source: Stacks Tags 0B56 and 07A7; node steps 2–4
(blueprint: lem-sf-tensor-square-mate-transfer). -/
noncomputable def tensorSquareMateCommonTranspose
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (ar : Pr ⊣ Rr)
    (Pi : D ⥤ C) (J : C ⥤ D) (K : A ⥤ B)
    (TA : A × A ⥤ A) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (di : (J.prod (𝟭 D)) ⋙ TD ⟶ ((𝟭 C).prod Pi) ⋙ TC ⋙ J)
    (a : J ⋙ Pp ⟶ Pr ⋙ K) (M : A) (N : D) :
    Pp.obj (TD.obj (J.obj (Rr.obj M), N)) ⟶
      K.obj (TA.obj (M, Pr.obj (Pi.obj N))) :=
  Pp.map (di.app (Rr.obj M, N)) ≫ a.app (TC.obj (Rr.obj M, Pi.obj N)) ≫
    K.map (muR.app (Rr.obj M, Pi.obj N) ≫
      TA.map (Prod.mkHom (ar.counit.app M) (𝟙 (Pr.obj (Pi.obj N)))))

/-- Mixed tensor-action compatibility transfers to the proper-adjunction mates.
Both displayed paths are components of one natural transformation, and each has the
specified common transpose. No comparison except `theta` is required to be invertible.

Source: Stacks Tags 0B56 and 07A7; agent mixed-action calculation, node steps 1–6
(blueprint: lem-sf-tensor-square-mate-transfer).

Proof:
1. The inverse adjunction bijection sends `b` to `P(b)` followed by the counit.
Its naturality transports pre- and postcomposition. `mateEquiv_counit` gives the
transpose of `g`, namely `a` followed by `K(epsilon_r)`. The defining transpose of
`rightAdjointProjectionMap` is `mu` followed by counit tensor identity.
2. Transpose the first path. Naturality of `a` at `pi_r` moves `P_p J(pi_r)` past
`a`. The counit identity for `pi_r` reduces the result to `P_p(d_i)`, then `a`, then
`K(c)`, exactly `tensorSquareMateCommonTranspose`.
3. Transpose the second path. Naturality of `muP` moves `P_p(g tensor 1)` through
the tensor comparison. The mate counit identity replaces `epsilon_p P_p(g)` by
`K(epsilon_r) a`.
4. Naturality of `dk` at `epsilon_r` moves that counit to the final tensor factor.
Bifunctoriality separates it from `a`. The assumed mixed square at `H = Rr M`
then identifies the preceding factors with `P_p(d_i)`, `a`, and `K(muR)`.
Cancel the specified identification with its inverse to obtain the same `K(c)`.
5. Injectivity of the inverse hom bijection gives equality. Counit and comparison
naturality give naturality of the projections in both variables; the mate is natural
by `mateEquiv`, and the mixed actions are natural by their types. Composing gives
one natural transformation whose components are both paths.
6. For ringed sites the maps in `ringedProjectionMateExact` are the same
counit-defined projections; the identification is recorded below. The argument uses
no inverses of `a`, its mate, the projections, tensor comparisons or mixed actions,
and no exactness, boundedness or Tor assumptions. -/
theorem tensorSquare_mate_transfer
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (Rp : B ⥤ D)
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (Pi : D ⥤ C) (Pk : B ⥤ A)
    (J : C ⥤ D) (K : A ⥤ B) (theta : Pi ⋙ Pr ≅ Pp ⋙ Pk)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (di : (J.prod (𝟭 D)) ⋙ TD ⟶ ((𝟭 C).prod Pi) ⋙ TC ⋙ J)
    (dk : (K.prod (𝟭 B)) ⋙ TB ⟶ ((𝟭 A).prod Pk) ⋙ TA ⋙ K)
    (a : J ⋙ Pp ⟶ Pr ⋙ K)
    (square : ∀ (H : C) (N : D),
      Pp.map (di.app (H, N)) ≫ a.app (TC.obj (H, Pi.obj N)) ≫
        K.map (muR.app (H, Pi.obj N)) ≫
        K.map (TA.map (Prod.mkHom (𝟙 (Pr.obj H)) (theta.hom.app N))) =
      muP.app (J.obj H, N) ≫
        TB.map (Prod.mkHom (a.app H) (𝟙 (Pp.obj N))) ≫ dk.app (Pr.obj H, Pp.obj N)) :
    ∃ t : ((Rr ⋙ J).prod (𝟭 D)) ⋙ TD ⟶
        ((𝟭 A).prod (Pi ⋙ Pr)) ⋙ TA ⋙ K ⋙ Rp,
      ∀ (M : A) (N : D),
        t.app (M, N) = tensorSquareMateFirst Pr Rr Pp Rp ar ap Pi J K
          TA TC TD muR di a M N ∧
        t.app (M, N) = tensorSquareMateSecond Pr Rr Pp Rp ar ap Pi Pk J K theta
          TA TB TD muP dk a M N ∧
        (ap.homEquiv _ _).symm
          (tensorSquareMateFirst Pr Rr Pp Rp ar ap Pi J K TA TC TD muR di a M N) =
            tensorSquareMateCommonTranspose Pr Rr Pp ar Pi J K TA TC TD muR di a M N ∧
        (ap.homEquiv _ _).symm
          (tensorSquareMateSecond Pr Rr Pp Rp ar ap Pi Pk J K theta TA TB TD muP dk a M N) =
            tensorSquareMateCommonTranspose Pr Rr Pp ar Pi J K TA TC TD muR di a M N := by
  let g := (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a))
  have first (M : A) (N : D) :
      (ap.homEquiv _ _).symm
        (tensorSquareMateFirst Pr Rr Pp Rp ar ap Pi J K TA TC TD muR di a M N) =
      tensorSquareMateCommonTranspose Pr Rr Pp ar Pi J K TA TC TD muR di a M N := by
    rw [tensorSquareMateFirst, ap.homEquiv_naturality_left_symm,
      ap.homEquiv_naturality_left_symm, ap.homEquiv_counit, mateEquiv_counit]
    have ha := a.naturality
      (tensorSquareProjectionMap Pr Rr ar TC TA muR M (Pi.obj N))
    change Pp.map (J.map _) ≫ a.app _ = a.app _ ≫ K.map (Pr.map _) at ha
    rw [reassoc_of% ha, ← K.map_comp]
    have hp := projection_transpose Pr Rr ar TC TA muR M (Pi.obj N)
    rw [ar.homEquiv_counit] at hp
    rw [hp]
    rfl
  have second (M : A) (N : D) :
      (ap.homEquiv _ _).symm
        (tensorSquareMateSecond Pr Rr Pp Rp ar ap Pi Pk J K theta
          TA TB TD muP dk a M N) =
      tensorSquareMateCommonTranspose Pr Rr Pp ar Pi J K TA TC TD muR di a M N := by
    rw [tensorSquareMateSecond, ap.homEquiv_naturality_left_symm,
      ap.homEquiv_naturality_right_symm]
    erw [projection_transpose Pp Rp ap TD TB muP (K.obj M) N]
    have hm := muP.naturality (Prod.mkHom (g.app M) (𝟙 N))
    change Pp.map (TD.map (Prod.mkHom (g.app M) (𝟙 N))) ≫ muP.app _ =
      muP.app _ ≫ TB.map (Prod.mkHom (Pp.map (g.app M)) (Pp.map (𝟙 N))) at hm
    simp only [Functor.map_id] at hm
    simp only [Category.assoc]
    erw [reassoc_of% hm]
    have ht : TB.map (Prod.mkHom (Pp.map (g.app M)) (𝟙 (Pp.obj N))) ≫
        TB.map (Prod.mkHom (ap.counit.app (K.obj M)) (𝟙 (Pp.obj N))) =
      TB.map (Prod.mkHom (a.app (Rr.obj M)) (𝟙 (Pp.obj N))) ≫
        TB.map (Prod.mkHom (K.map (ar.counit.app M)) (𝟙 (Pp.obj N))) := by
      rw [← TB.map_comp, ← TB.map_comp]
      congr 1
      ext
      · exact mateEquiv_counit ar ap (TwoSquare.mk J Pr Pp K a) M
      · simp
    rw [reassoc_of% ht]
    have hd := dk.naturality (Prod.mkHom (ar.counit.app M) (𝟙 (Pp.obj N)))
    change TB.map (Prod.mkHom (K.map (ar.counit.app M)) (𝟙 (Pp.obj N))) ≫
        dk.app (M, Pp.obj N) =
      dk.app (Pr.obj (Rr.obj M), Pp.obj N) ≫
        K.map (TA.map (Prod.mkHom (ar.counit.app M) (Pk.map (𝟙 (Pp.obj N))))) at hd
    simp only [Functor.map_id] at hd
    rw [reassoc_of% hd, ← reassoc_of% (square (Rr.obj M) N)]
    simp only [← K.map_comp, ← TA.map_comp]
    simp [tensorSquareMateCommonTranspose]
  refine ⟨{ app := fun X ↦ tensorSquareMateFirst Pr Rr Pp Rp ar ap Pi J K
              TA TC TD muR di a X.1 X.2
            naturality := ?_ }, ?_⟩
  · intro X Y f
    have hi := di.naturality (Prod.mkHom (Rr.map f.1) f.2)
    have hp := (projectionNatTrans Pr Rr ar TC TA muR).naturality
      (Prod.mkHom f.1 (Pi.map f.2))
    have hg := g.naturality (TA.map (Prod.mkHom f.1 (Pr.map (Pi.map f.2))))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hi hp hg ⊢
    simp only [tensorSquareMateFirst, Category.assoc]
    rw [reassoc_of% hi, ← J.map_comp_assoc]
    change _ ≫ J.map (_ ≫ tensorSquareProjectionMap Pr Rr ar TC TA muR _ _) ≫ _ = _
    dsimp only [projectionNatTrans] at hp
    erw [hp]
    simp only [Functor.map_comp, Category.assoc]
    rw [hg]
  · intro M N
    refine ⟨rfl, ?_, first M N, second M N⟩
    exact (ap.homEquiv _ _).symm.injective ((first M N).trans (second M N).symm)

end CategoryTheory

namespace SheafOfModules

end SheafOfModules
