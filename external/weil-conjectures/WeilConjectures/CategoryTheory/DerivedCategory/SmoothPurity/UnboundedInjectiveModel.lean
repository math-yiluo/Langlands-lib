/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.SmoothPurity.FunctorialInjectiveComplexEmbedding

/-!
# Unbounded injective models

Source: Stacks Project, Tag 079P, the injective model construction.
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty ZeroObject

namespace DerivedCategory

/-- Every derived object in a Grothendieck abelian category has a K-injective model
with injective terms.
Source: Stacks Project, Tag 079P, using the functorial injective complex embedding.
(blueprint: lem-pur-unbounded-injective-model).

Proof: Factor a complex-to-zero map by the monomorphic quasi-isomorphism weak
factorization system. Its middle complex I is K-injective and has the right lifting
property. Embed I by a monomorphic quasi-isomorphism through injective subobjects in
each degree. The lifting property retracts that embedding, so each I^n is a retract of
an injective object. Localizing the original factorization gives the required model. -/
theorem nonempty_injectiveModel
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory C] (M : DerivedCategory C) : Nonempty M.InjectiveModel := by
  let K := Q.objPreimage M
  let F := functorialFactorizationData (HomologicalComplex.monoQuasiIso C (.up ℤ))
    (HomologicalComplex.monoQuasiIso C (.up ℤ)).rlp
  let a := (CochainComplex.toArrowZero C).obj K
  let I : CochainComplex C ℤ := F.Z.obj a
  have hI : CochainComplex.IsKInjective I := CochainComplex.isKInjective_of_rlp (F.p.app a)
    (isZero_zero _) (F.hp a)
  obtain ⟨N, j, hj⟩ := CochainComplex.exists_functorial_injective_complex_embedding C
  have hm : Mono (j.app I) := HomologicalComplex.mono_of_mono_f _ (hj I).1
  have hq : QuasiIso (j.app I) := (hj I).2.1
  have hl := F.hp a (j.app I) ⟨hm, hq⟩
  let sq : CommSq (𝟙 I) (j.app I) (F.p.app a) (0 : N.obj I ⟶ 0) :=
    ⟨(isZero_zero _).eq_of_tgt _ _⟩
  have hi (n : ℤ) : Injective (I.X n) := by
    obtain ⟨J, b, c, hJ, _, hbc⟩ := (hj I).2.2 n
    let : Injective J := hJ
    apply Retract.injective (Y := J)
    refine ⟨b, c ≫ sq.lift.f n, ?_⟩
    rw [← Category.assoc, hbc]
    exact congrArg (fun f ↦ f.f n) sq.fac_left
  have hmono : Mono (F.i.app a) := (F.hi a).1
  have hquasi : QuasiIso (F.i.app a) := (F.hi a).2
  let : IsIso (Q.map (F.i.app a)) := by
    rw [isIso_Q_map_iff_quasiIso]
    exact hquasi
  exact ⟨{
    I := I
    injective := hi
    isKInjective := hI
    iso := (asIso (Q.map (F.i.app a))).symm ≪≫ Q.objObjPreimageIso M }⟩

end DerivedCategory
