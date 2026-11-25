/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.TorsorIso
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.AdjoinRootCoverFiniteEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-! # The Artin–Schreier cover as an étale torsor

The Artin–Schreier cover of `f` is an `𝔽_p`-torsor over `S` (`Scheme.EtaleTorsor`), whose
sheaf torsor under the constant sheaf `𝔽_p` is the functor of points of the cover, the constant
section `a` acting by the translation `T ↦ T + a`.
Source: blueprint, lemma-artin-schreier-character-sheaf, step (5);
lem-weil-pbc-small-etale-representable-presheaf-sheaf.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial Opposite

noncomputable section

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{u}} {f : Γ(S, ⊤)} {P : Polynomial Γ(S, ⊤)}

/-- The Artin–Schreier polynomial is monic. -/
lemma monic_of_eq_artinSchreier (hP : P = X ^ p - X - C f) : P.Monic :=
  hP ▸ monic_artinSchreier p S f

omit [Fact p.Prime] in
/-- In characteristic `p` the derivative of the Artin–Schreier polynomial is a unit modulo it. -/
lemma isUnit_derivative_of_eq_artinSchreier (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) : IsUnit (AdjoinRoot.mk P (derivative P)) := by
  have h : derivative P = -1 := by rw [hP, derivative_artinSchreier p S f hchar]
  rw [h, map_neg, map_one]
  exact isUnit_one.neg

/-- The Artin–Schreier cover is finite. -/
lemma isFinite_artinSchreier (hP : P = X ^ p - X - C f) : IsFinite (adjoinRootCover S P).hom :=
  isFinite_adjoinRootCover S P (monic_of_eq_artinSchreier hP)

/-- The Artin–Schreier cover is étale. -/
lemma etale_artinSchreier (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    Etale (adjoinRootCover S P).hom :=
  etale_adjoinRootCover S P (monic_of_eq_artinSchreier hP)
    (isUnit_derivative_of_eq_artinSchreier hP hchar)

/-- The Artin–Schreier cover is finite locally free of degree `p`. -/
lemma isFiniteLocallyFreeOfDegree_artinSchreier (hP : P = X ^ p - X - C f) :
    (adjoinRootCover S P).hom.IsFiniteLocallyFreeOfDegree p := by
  have h := isFiniteLocallyFreeOfDegree_adjoinRootCover S P (monic_of_eq_artinSchreier hP)
  refine { toIsFiniteLocallyFree := h.toIsFiniteLocallyFree, fiberDegree_eq := fun x ↦ ?_ }
  have : Nontrivial Γ(S, ⊤) := (S.presheaf.Γgerm x).hom.domain_nontrivial
  rw [h.fiberDegree_eq x, hP, natDegree_artinSchreier]

/-- **The Artin–Schreier cover as an étale torsor** under `𝔽_p`, acting by translations. -/
def artinSchreierEtaleTorsor (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    Scheme.EtaleTorsor (ULift.{u + 1} (ZMod p)) S where
  P := (adjoinRootCover S P).left
  π := (adjoinRootCover S P).hom
  isFinite := isFinite_artinSchreier hP
  etale := etale_artinSchreier hP hchar
  surjective := surjective_adjoinRootCover_artinSchreier hP hchar
  vadd m := artinSchreierTranslation hP hchar m.down
  vadd_π m := artinSchreierTranslation_hom hP hchar m.down
  zero_vadd := artinSchreierTranslation_zero hP hchar
  add_vadd m n := artinSchreierTranslation_add hP hchar m.down n.down
  isIso_sigmaDesc := isIso_artinSchreier_sigmaDesc hP hchar

/-- The functor of points of the Artin–Schreier cover, computed on the small étale site or on
the category of all schemes over `S`. -/
def artinSchreierSheafTorsorIso (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    (artinSchreierEtaleTorsor hP hchar).toSheafTorsor.sheaf.obj ≅
      (Scheme.Etale.forget S).op ⋙ yoneda.obj (adjoinRootCover S P) ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (Equiv.ulift.trans
      (((Scheme.Etale.forgetFullyFaithful S).homEquiv).trans Equiv.ulift.symm)))
    (fun g ↦ by
      ext x
      exact ULift.ext ((Scheme.Etale.forget S).map_comp _ _))

lemma artinSchreierSheafTorsorIso_hom_app (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) (U : S.Etaleᵒᵖ)
    (s : (artinSchreierEtaleTorsor hP hchar).toSheafTorsor.sheaf.obj.obj U) :
    ((artinSchreierSheafTorsorIso hP hchar).hom.app U s).down =
      (Scheme.Etale.forget S).map s.down :=
  rfl

/-- **The sheaf torsor of the Artin–Schreier cover.** The functor of points of the cover is a
torsor under the constant sheaf `𝔽_p` on the small étale site, on which the constant section
`a` acts by the translation by `a`. -/
theorem artinSchreier_sheafTorsor (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0) :
    ∃ (R : Sheaf.Torsor
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))))
        (e : R.sheaf.obj ≅ (Scheme.Etale.forget S).op ⋙
          yoneda.obj (adjoinRootCover S P) ⋙ uliftFunctor.{u + 1}),
      ∀ (U : S.Etale) (a : ZMod p) (s : R.sheaf.obj.obj (Opposite.op U)),
        (e.hom.app (Opposite.op U)
          (R.vadd (Opposite.op U)
            (((toSheafify S.smallEtaleTopology
              ((Functor.const S.Etaleᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app
                  (Opposite.op U)) (ULift.up a)) s)).down =
          (e.hom.app (Opposite.op U) s).down ≫
            (artinSchreierAction hP hchar (Multiplicative.ofAdd a)).asIso.hom := by
  let : TopologicalSpace (ULift.{u + 1} (ZMod p)) := ⊥
  have : DiscreteTopology (ULift.{u + 1} (ZMod p)) := ⟨rfl⟩
  refine ⟨(artinSchreierEtaleTorsor hP hchar).toSheafTorsor,
    artinSchreierSheafTorsorIso hP hchar, fun U a s ↦ ?_⟩
  rw [artinSchreierSheafTorsorIso_hom_app, artinSchreierSheafTorsorIso_hom_app]
  have hc : (Scheme.Etale.constantSheafIsoContinuousMapSheaf S (ULift.{u + 1} (ZMod p))).hom.hom.app
      (op U) ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app (op U) (ULift.up a)) =
      ContinuousMap.const _ (ULift.up a) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (Scheme.Etale.toSheafify_constantSheafToContinuousMapSheaf S (ULift.{u + 1} (ZMod p)))
      (op U)) (ULift.up a)
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h
  refine Over.OverMorphism.ext ?_
  have h := (artinSchreierEtaleTorsor hP hchar).smulHom_const (U := U) (ULift.up a) s.down
  exact (congr_arg (fun c ↦ ((artinSchreierEtaleTorsor hP hchar).smulHom c s.down).left) hc).trans h

end AlgebraicGeometry
