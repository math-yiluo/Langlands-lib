/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluation
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.SelfExtPushforwardHomology
import WeilConjectures.AlgebraicGeometry.SelfTorPushforwardHomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.SelfExtTorResolutionLocal

/-! # A common complex model for self Ext and self Tor

Source: Stacks Project, Tags 08DH, 08I3, 08KS, 0BQY and 068G.
(blueprint: lem-sc-self-ext-tor-resolution-model). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Self Ext and self Tor are computed on the closed subscheme by one complex T and
an injective resolution J of its structure sheaf. On regular affine charts T has
a finite free zero-differential model. This statement supplies no comparison map
from Ext to dual Tor and asserts no invertibility of such a map.

Source: Stacks Project, cohomology.tex, section-internal-hom (08DH), its derived
pullback evaluation mate (08I3); modules.tex,
lemma-i-star-equivalence (08KS); duality.tex, lemma-regular-ideal-ext (0BQY),
Koszul computation with quotient coefficients; more-algebra.tex,
equation-simple-tor-product (068G), resolution computation of Tor.
(blueprint: lem-sc-self-ext-tor-resolution-model).

Proof: Choose a K-flat resolution P of B[0] with flat terms and a K-injective
resolution J of O_Z[0]; the tensor pullback is additive by its adjunction with
pushforward. Represent the derived pullback Li*B on Z by the ordinary tensor pullback
of a K-flat resolution of B=i_*O_Z on Y; call this complex T. Choose a K-injective
resolution J of O_Z. It has cohomology O_Z in degree zero and zero elsewhere.
The internal derived pullback/direct-image adjunction identifies RHom_Y(B,i_*O_Z)
with i_*RHom_Z(Li*B,O_Z). To see this identification, test against an arbitrary
derived object A on Y: tensor--Hom adjunction gives Hom(A tensor B,i_*O_Z),
derived pullback/direct-image adjunction gives Hom(Li*(A tensor B),O_Z),
and the pullback tensor comparison followed by tensor--Hom and the same
adjunction gives Hom(A,i_*RHom_Z(Li*B,O_Z)). Naturality and Yoneda identify
the two objects. Closed-immersion direct image is exact and fully faithful,
so its cohomology is i_*H^n(Hom(T,J)). Its tensor-pullback counit identifies
ordinary i* of that cohomology with H^n(Hom(T,J)), giving eG. Similarly the derived
projection formula identifies B tensor^L_Y B with i_*(Li*B); exact direct image
and its counit give eQ. These computations use the fixed derived tensor on Y,
and their comparison does not change the supplied derived universe.
On an affine U with quotient A/I, use the Koszul projective resolution of A/I
and its sheafified augmentation. Restricting T to the inverse-image chart gives
the same derived pullback, hence a quasi-isomorphism roof to the sheafification
of K_A(f) tensor_A A/I. Every f_j vanishes in A/I, so every differential of that
complex vanishes. Its exterior-power terms are finite free, with degrees from
-minus-m to zero. Restricting further to V and the indicated over site preserves
these properties and the two quasi-isomorphisms. Open restriction preserves
K-injectivity of J. Thus the same T and J give all the chart models simultaneously;
no chartwise choices are used to choose a global morphism. For m=0 the model has
one term; for n>m the relevant homology vanishes. Empty charts and I=A give zero
models. No proper-ideal or positive-length hypothesis is needed. -/
theorem exists_selfExt_tor_resolution_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ (T J : CochainComplex Z.Modules ℤ)
      (_ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
      (_ : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
      (_ : (Scheme.Modules.tensorPullback i).obj G ≅
        (homComplex (R := Z.sheaf) T J).homology (n : ℤ))
      (_ : Q ≅ T.homology (-(n : ℤ))),
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
        let Fc := moduleOpenOverComplexFunctor Z V W
        CochainComplex.IsKInjective (Fc.obj J) ∧
          HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) := by
  classical
  dsimp
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction i
  have hAdd : (Scheme.Modules.tensorPullback i).Additive := adj.left_adjoint_additive
  obtain ⟨P, a, hP, hflat, ha, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := Y.sheaf) ((HomologicalComplex.single Y.Modules (.up ℤ) 0).obj B)
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology Z) Z.sheaf
  let O := (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let J := I.obj O
  let b := η.app O
  obtain ⟨hb, hKI, _⟩ := hI O
  have : QuasiIso b := hb
  have hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k) := by
    intro k hk
    exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      (SheafOfModules.unit Z.ringCatSheaf) k hk).of_iso
        (isoOfQuasiIsoAt b k).symm
  let e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf :=
    (isoOfQuasiIsoAt b 0).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨g⟩ := nonempty_selfExt_pushforward_homology i P J a b ⟨ha, hP⟩ hb hKI (n : ℤ)
  obtain ⟨q⟩ := nonempty_selfTor_pushforward_homology i P a ⟨ha, hP⟩ (-(n : ℤ))
  let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  have hc : ∀ N : Z.Modules, IsIso (e.counit.app N) :=
    (closedImmersion_pushforward_fullyFaithful i).1
  let eG := (Scheme.Modules.tensorPullback i).mapIso g ≪≫
    asIso (e.counit.app ((homComplex (R := Z.sheaf) T J).homology (n : ℤ)))
  let eQ := (Scheme.Modules.tensorPullback i).mapIso q ≪≫
    asIso (e.counit.app (T.homology (-(n : ℤ))))
  exact ⟨T, J, hJ, e0, eG, eQ,
    selfExt_tor_resolution_local i P J a b ⟨ha, hP⟩ hflat hb hKI⟩

end AlgebraicGeometry
