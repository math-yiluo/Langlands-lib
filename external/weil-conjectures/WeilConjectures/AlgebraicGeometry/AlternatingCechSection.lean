/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.SignedCechExtension

/-!
# Ordered restriction admits a cochain section

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Ordered restriction admits a cochain section.

Source: Stacks Project, Cohomology of Sheaves, Tags 01FJ and 01FK.
(blueprint: lem-pc-alternating-cech-section)

Proof: Construct signed extension on ordered coordinates by sorting every injective
tuple, multiplying by its sorting sign, and restricting along the corresponding
index map; on repeated tuples use zero. This is additive and is the identity on
increasing tuples. Composing with e gives degree maps f, and hr shows f_p followed
by r_p is the identity. Apply the chain-map equation for r to f_p(a): the ordered
coordinates of d(f_p(a)) are e_{p+1}(d_A(a)). The signed-extension differential
lemma says d(f_p(a)) is the signed extension of these coordinates, which is exactly
f_{p+1}(d_A(a)). The degree maps therefore assemble into a cochain map i, and their
section identities imply i followed by r is the identity. -/
theorem alternatingCechRestrictionHomotopy_map (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (A : CochainComplex AddCommGrpCat.{max v w} ℕ)
    (e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))))
    (r : S.complex F ⟶ A)
    (hr : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (e p).hom ((r.f p) s) t = s t.1) :
    ∃ i : A ⟶ S.complex F, i ≫ r = 𝟙 A := by
  let f (p : ℕ) : A.X p ⟶ (S.complex F).X p :=
    (e p).hom ≫ signedCechExtension X U F S p
  have hf (p : ℕ) : f p ≫ r.f p = 𝟙 (A.X p) := by
    apply (cancel_mono (e p).hom).mp
    apply AddCommGrpCat.ext
    intro a
    funext t
    change (e p).hom ((r.f p) (f p a)) t = (e p).hom a t
    rw [hr]
    exact signedCechExtension_increasing X U F S p ((e p).hom a) t
  have hcomm (p : ℕ) : f p ≫ (S.complex F).d p (p + 1) =
      A.d p (p + 1) ≫ f (p + 1) := by
    apply AddCommGrpCat.ext
    intro a
    have ha : (r.f p) (f p a) = a := by
      exact congrArg (fun k : A.X p ⟶ A.X p ↦ k a) (hf p)
    have hd : (r.f (p + 1)) (S.differentialValue F p (f p a)) =
        A.d p (p + 1) a := by
      have h := congrArg (fun k ↦ k (f p a)) (r.comm p (p + 1))
      simp only [SiteCechComplex.complex, CochainComplex.of_d,
        ConcreteCategory.comp_apply] at h
      change A.d p (p + 1) ((r.f p) (f p a)) =
        (r.f (p + 1)) (S.differentialValue F p (f p a)) at h
      rw [ha] at h
      exact h.symm
    have he : (fun t : {t : Fin (p + 1 + 1) → I // StrictMono t} ↦
        S.differentialValue F p (f p a) t.1) =
        (e (p + 1)).hom (A.d p (p + 1) a) := by
      funext t
      rw [← hr (p + 1) (S.differentialValue F p (f p a)) t, hd]
    simp only [SiteCechComplex.complex, CochainComplex.of_d,
      ConcreteCategory.comp_apply]
    change S.differentialValue F p
        (signedCechExtension X U F S p ((e p).hom a)) =
      signedCechExtension X U F S (p + 1) ((e (p + 1)).hom (A.d p (p + 1) a))
    rw [signedCechExtension_differential]
    exact congrArg (signedCechExtension X U F S (p + 1)) he
  refine ⟨CochainComplex.ofHom f hcomm, ?_⟩
  apply HomologicalComplex.hom_ext
  intro p
  exact hf p

end AlgebraicGeometry.Scheme
