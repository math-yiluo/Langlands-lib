/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.ResolutionOpenScalarComparison
import WeilConjectures.AlgebraicGeometry.TensorUnitPowerScalar

/-! # Resolution sections and tensor powers of the unit

Source: Stacks Project, Tags 01E1, 01E4 and 09MR.
(blueprint: lem-pc-resolution-unit-twist-comparison).
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Compare raw resolution cohomology with cohomology twisted by powers of the unit.
The comparison preserves restriction and identifies the tensor transition with scalar
multiplication. This is a comparison assertion, with no localization or torsion conclusion.

Source: Stacks Project, Tag 01E4, proof of Lemma 20.7.3; Tag 01E1,
Lemma 20.7.1; Tag 09MR, tensor-unit specialization of the numerator maps.
(blueprint: lem-pc-resolution-unit-twist-comparison).

Proof: Write Y = f inverse W and G = F restricted to Y. Pull a back by the
structure-sheaf map on W and restrict to the top open of Y, obtaining b.
Take s to be b times the standard generator of the tensor unit on Y. Its
nonvanishing open is the inverse image of D(a), viewed inside Y: on each
stalk the unit generator identifies its fibre with the residue field, so s
is nonzero in that fibre exactly where b is a unit in the local ring.
Restriction to Y preserves exactness and injectives by 01E1. The restricted
resolution therefore computes open module cohomology on Y and on every open
U with the displayed nonvanishing locus. Evaluate f_*I on W and D(a).
Degreewise, these complexes are precisely the sections of that restricted
resolution on Y and U. Evaluation preserves kernels and cokernels, so its
homology comparison identifies P(W) and P(D(a)) with these cohomology groups.
The comparison is natural in restrictions because the degreewise maps are
restriction of the very same sections. For every n, identify the nth tensor
power of the unit with the unit, recursively using the unitors, and then
identify G tensor that power with G by its right unitor. Applying open
cohomology and composing the inverses of these isomorphisms gives e(n) and d.
Under these identifications, mulTensorPowSection(s,G,0,n) is multiplication
by b^n: evaluate on a pure tensor and use s=b times the unit generator,
then the associator and unitors send that tensor to b^n times its G factor.
The section-complex comparison is semilinear for the pullback map on rings;
hence multiplication by b^n corresponds to multiplication by a^n on P(W).
Taking homology gives the second equation. The first is the restriction
naturality already established. This argument uses no affineness, compactness,
quasi-separatedness or quasi-coherence. For a=0 the nonvanishing open is empty;
for a a unit it is all of Y. Empty W, zero F and degree zero are covered by
the same section-complex and unitor isomorphisms. -/
theorem resolution_unitTwist_comparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    ∃ (s : Γ(L, ⊤))
      (e : ∀ n : ℕ, P.obj (op W) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules)),
      (∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus L s →
        ∃ d : P.obj (op (T.basicOpen a)) ≃+
          (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj
            (G ⊗ L.tensorPow 0 : Y.Modules),
          ∀ x : P.obj (op W),
            (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
              (homOfLE (le_top : U ≤ ⊤))).app (G ⊗ L.tensorPow 0 : Y.Modules)
                (e 0 x) = d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x)) ∧
      (∀ (n : ℕ) (x : P.obj (op W)),
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
          (mulTensorPowSection (homOfGlobalSection L s) G 0 n) (e 0 x) =
            e (0 + n) (a ^ n • x)) := by
  classical
  dsimp only
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let L := 𝟙_ Y.Modules
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
  let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
  let H := RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤
  obtain ⟨c, hres, hscalar⟩ := resolution_open_scalar_comparison f F I q W a
  obtain ⟨i, hi⟩ := tensorUnitPower_scalar Y G b
  let e (n : ℕ) : P.obj (op W) ≃+ H.obj (G ⊗ L.tensorPow n : Y.Modules) :=
    c.trans (H.mapIso (i n).symm).addCommGroupIsoToAddEquiv
  refine ⟨s, e, ?_, ?_⟩
  · intro U hU
    obtain ⟨d, hd⟩ := hres U hU
    let HU := RingedSpace.openModuleCohomology Y.toRingedSpace q U
    refine ⟨d.trans (HU.mapIso (i 0).symm).addCommGroupIsoToAddEquiv, ?_⟩
    intro x
    have hn := (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
      (homOfLE (le_top : U ≤ ⊤))).naturality (i 0).inv
    have hx := ConcreteCategory.congr_hom hn (c x)
    change _ = HU.map (i 0).inv (d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x))
    change _ = HU.map (i 0).inv
      ((RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
        (homOfLE (le_top : U ≤ ⊤))).app G (c x)) at hx
    exact hx.trans (congrArg (HU.map (i 0).inv) (hd x))
  · intro n x
    apply (H.mapIso (i (0 + n))).addCommGroupIsoToAddEquiv.injective
    change H.map (i (0 + n)).hom
      (H.map (mulTensorPowSection (homOfGlobalSection L s) G 0 n)
        (H.map (i 0).inv (c x))) =
      H.map (i (0 + n)).hom (H.map (i (0 + n)).inv (c (a ^ n • x)))
    rw [← Functor.map_comp_apply, hi n]
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    change H.map (G.smulHom (b ^ n))
      ((H.mapIso (i 0)).hom ((H.mapIso (i 0)).inv (c x))) =
        (H.mapIso (i (0 + n))).hom
          ((H.mapIso (i (0 + n))).inv (c (a ^ n • x)))
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
    exact hscalar n x

end AlgebraicGeometry.Scheme.Modules
