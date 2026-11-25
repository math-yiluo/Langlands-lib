/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotientLine
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientRootProjectionIso

/-! # A single quotient root endpoint

Source: diagonal tower coefficient changes, paragraph (1), the finite Tate-line reduction.
(blueprint: lem-diagonal-quotient-root-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] QuotientLineRealization quotientLine quotientLineMap
  comparisonUpperStar comparisonAdjunction forgetComparisonIso
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem realizedFree_bijective
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f : e.F.obj ((Mod.free (condensedRingObj R X)).obj G) ⟶ N ↦
      (Mod.freeForgetAdjunction (condensedRingObj R X)).unit.app G ≫
        e.underlying.inv.app ((Mod.free (condensedRingObj R X)).obj G) ≫
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map f) := by
  let B := condensedRingObj R X
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let M := (Mod.free B).obj G
  let η : G ⟶ M.X := (Mod.freeForgetAdjunction B).unit.app G
  have hK (K : Modules R X) : Function.Bijective
      (fun f : e.F.obj M ⟶ e.F.obj K ↦ η ≫ e.underlying.inv.app M ≫ U.map f) := by
    have hb : Function.Bijective
        (fun f : M ⟶ K ↦ η ≫ e.underlying.inv.app M ≫ U.map (e.F.map f)) := by
      let h := ((Mod.freeForgetAdjunction B).homEquiv G K).trans
        (Iso.homCongr (Iso.refl G) (e.underlying.symm.app K))
      convert h.bijective using 1
      funext f
      dsimp only [h, Equiv.trans_apply, Iso.homCongr_apply]
      rw [Adjunction.homEquiv_unit]
      change η ≫ e.underlying.inv.app M ≫ U.map (e.F.map f) =
        (η ≫ f.hom) ≫ e.underlying.inv.app K
      simpa only [Functor.comp_map, Mod.forget, Category.assoc] using
        congrArg (fun z ↦ η ≫ z) (e.underlying.inv.naturality f).symm
    let ff := Functor.FullyFaithful.ofFullyFaithful e.F
    constructor
    · intro f g h
      obtain ⟨f', rfl⟩ := ff.map_surjective f
      obtain ⟨g', rfl⟩ := ff.map_surjective g
      exact congrArg e.F.map (hb.1 h)
    · intro v
      obtain ⟨f, hf⟩ := hb.2 v
      exact ⟨e.F.map f, hf⟩
  let K := e.F.asEquivalence.inverse.obj N
  let c : e.F.obj K ≅ N := e.F.asEquivalence.counitIso.app N
  let h := (Iso.homCongr (Iso.refl (e.F.obj M)) c.symm).trans
    ((Equiv.ofBijective _ (hK K)).trans
      (Iso.homCongr (Iso.refl G) (U.mapIso c)))
  convert h.bijective using 1
  funext f
  simp only [h, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.symm_hom, Functor.mapIso_hom,
    Category.id_comp, Category.assoc]
  rw [U.map_comp]
  simp only [Category.assoc, ← U.map_comp,
    c.inv_hom_id, Category.comp_id]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem etaleLineHom_eq
    (X : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : Scheme.finiteEtaleTateLine X N A hA ⟶ P) :
    Scheme.lineHomEquiv X N A hA P f =
      Etale.ordinaryFiniteRootMap A N hA X ≫
        (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map f := by
  ext W z
  rw [Scheme.lineHomEquiv_generator]
  change f.hom.app W _ = f.hom.app W _
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private def cartierRootHomEquiv
    (X : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (r : FiniteRoots X N)
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (geoCartierLine A N hA X ⟶ P) ≃
      (Scheme.proEtaleRootsOfUnitySheaf X N ⟶
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj P) := by
  refine ((comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ P).trans ?_
  refine (Scheme.lineHomEquiv X N A hA
    ((comparisonLowerStar (ModuleCat.{u + 1} A) X).obj P)).trans ?_
  change (Scheme.rootsOfUnitySheaf X N ⟶
    (comparisonLowerStar Ab.{u + 1} X).obj
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj P)) ≃ _
  exact ((comparisonAdjunction Ab.{u + 1} X).homEquiv _ _).symm.trans
    (Iso.homCongr r.iso (Iso.refl _))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem cartierRootHomEquiv_eq
    (X : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (r : FiniteRoots X N)
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (f : geoCartierLine A N hA X ⟶ P) :
    cartierRootHomEquiv X N A hA r P f = r.toLine A hA ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map f := by
  dsimp only [cartierRootHomEquiv, Equiv.trans_apply, id]
  simp only [Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, FiniteRoots.toLine, Category.assoc]
  congr 1
  apply ((comparisonAdjunction Ab.{u + 1} X).homEquiv _ _).injective
  let Ue := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let Up := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let L := Scheme.finiteEtaleTateLine X N A hA
  let m := Etale.ordinaryFiniteRootMap A N hA X
  let b := (forgetComparisonIso A X).hom.app L
  let adj := comparisonAdjunction Ab.{u + 1} X
  let adjM := comparisonAdjunction (ModuleCat.{u + 1} A) X
  have hb : adj.homEquiv _ _ b = Ue.map (adjM.unit.app L) := by
    calc
      _ = adj.homEquiv _ _ ((adj.homEquiv _ _).symm
          (Ue.map (adjM.unit.app L))) :=
        congrArg (adj.homEquiv _ _) (forgetComparisonIso_hom A X L)
      _ = Ue.map (adjM.unit.app L) := Equiv.apply_symm_apply _ _
    rfl
  calc
    _ = Scheme.lineHomEquiv X N A hA ((comparisonLowerStar (ModuleCat.{u + 1} A) X).obj P)
        (adjM.homEquiv L P f) := Equiv.apply_symm_apply _ _
    _ = m ≫ Ue.map (adjM.homEquiv L P f) := etaleLineHom_eq X N A hA _ _
    _ = m ≫ Ue.map (adjM.unit.app L) ≫
        (comparisonLowerStar Ab.{u + 1} X).map (Up.map f) := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
      rfl
    _ = m ≫ adj.homEquiv _ _ b ≫
        (comparisonLowerStar Ab.{u + 1} X).map (Up.map f) :=
      congrArg (fun z ↦ m ≫ z ≫ (comparisonLowerStar Ab.{u + 1} X).map (Up.map f)) hb.symm
    _ = _ := by
      have h := adj.homEquiv_naturality_left m (b ≫ Up.map f)
      have h' := adj.homEquiv_naturality_right b (Up.map f)
      simpa only [Category.assoc] using
        (h.trans (congrArg (fun z ↦ m ≫ z) h')).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finiteFreeRootEndpoint
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (N : ℕ) (hA : (N : A) = 0) (r : FiniteRoots X N) :
    ∃ i : e.F.obj ((Mod.free (condensedRingObj R X)).obj
        (Scheme.proEtaleRootsOfUnitySheaf X N)) ≅ geoCartierLine A N hA X,
      (Mod.freeForgetAdjunction (condensedRingObj R X)).unit.app
          (Scheme.proEtaleRootsOfUnitySheaf X N) ≫
        e.underlying.inv.app ((Mod.free (condensedRingObj R X)).obj
          (Scheme.proEtaleRootsOfUnitySheaf X N)) ≫
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map i.hom = r.toLine A hA := by
  let G := Scheme.proEtaleRootsOfUnitySheaf X N
  let M := (Mod.free (condensedRingObj R X)).obj G
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let s := (Mod.freeForgetAdjunction (condensedRingObj R X)).unit.app G ≫
    e.underlying.inv.app M
  let t := r.toLine A hA
  have hs (P) : Function.Bijective (fun f : e.F.obj M ⟶ P ↦ s ≫ U.map f) := by
    simpa only [s, Category.assoc] using realizedFree_bijective e G P
  have ht (P) : Function.Bijective
      (fun f : geoCartierLine A N hA X ⟶ P ↦ t ≫ U.map f) := by
    convert (cartierRootHomEquiv X N A hA r P).bijective using 1
    funext f
    exact (cartierRootHomEquiv_eq X N A hA r P f).symm
  obtain ⟨g, hg⟩ := (hs (geoCartierLine A N hA X)).2 t
  obtain ⟨f, hf⟩ := (ht (e.F.obj M)).2 s
  change s ≫ U.map g = t at hg
  change t ≫ U.map f = s at hf
  have hgf : g ≫ f = 𝟙 _ := by
    apply (hs _).1
    change s ≫ U.map (g ≫ f) = s ≫ U.map (𝟙 _)
    rw [U.map_comp, U.map_id, ← Category.assoc, hg, hf]
    exact (Category.comp_id s).symm
  have hfg : f ≫ g = 𝟙 _ := by
    apply (ht _).1
    change t ≫ U.map (f ≫ g) = t ≫ U.map (𝟙 _)
    rw [U.map_comp, U.map_id, ← Category.assoc, hf, hg]
    exact (Category.comp_id t).symm
  refine ⟨⟨g, f, hgf, hfg⟩, ?_⟩
  simpa only [s, Category.assoc] using hg

private theorem endpointFromFree
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (N : ℕ) (hA : (N : A) = 0) (r : FiniteRoots X N)
    {M : Modules R X}
    (q : M ⟶ (Mod.free (condensedRingObj R X)).obj
      (Scheme.proEtaleRootsOfUnitySheaf X N)) [IsIso q]
    {L : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (m : L ⟶ M.X) (p : L ⟶ Scheme.proEtaleRootsOfUnitySheaf X N)
    (hq : m ≫ q.hom = p ≫ (Mod.freeForgetAdjunction (condensedRingObj R X)).unit.app
      (Scheme.proEtaleRootsOfUnitySheaf X N)) :
    Nonempty (e.LineEndpoint M (geoCartierLine A N hA X) m (p ≫ r.toLine A hA)) := by
  obtain ⟨i, hi⟩ := finiteFreeRootEndpoint e N hA r
  let T := (Mod.free (condensedRingObj R X)).obj (Scheme.proEtaleRootsOfUnitySheaf X N)
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let j := e.F.mapIso (asIso q) ≪≫ i
  refine ⟨⟨j, ?_⟩⟩
  unfold FiniteRealization.LineNormalization
  dsimp only [j, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [Functor.map_comp]
  have hn : e.underlying.inv.app M ≫ U.map (e.F.map q) =
      q.hom ≫ e.underlying.inv.app T := by
    exact (e.underlying.inv.naturality q).symm
  calc
    _ = m ≫ q.hom ≫ e.underlying.inv.app T ≫ U.map i.hom := by
      rw [← Category.assoc (e.underlying.inv.app M), hn]
      simp only [Category.assoc]
      rfl
    _ = p ≫ r.toLine A hA := by
      rw [← Category.assoc m, hq]
      simpa only [Category.assoc] using congrArg (fun z ↦ p ≫ z) hi

private theorem extendFreeProjection
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight Y)]
    {R B D : C} [MonObj R] [IsCommMonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] (a : R ⟶ D) [IsMonHom a]
    (r : B ⟶ D) [IsMonHom r] (ha : p ≫ r = a)
    (M : Mod C R) (G : C)
    (f : M ⟶ (Mod.comap p).obj ((Mod.free B).obj G))
    {L : C} (v : L ⟶ M.X) (w : L ⟶ G)
    (hf : v ≫ f.hom = w ≫ (Mod.freeForgetAdjunction B).unit.app G) :
    ∃ q : (Mod.extendScalars a).obj M ⟶ (Mod.free D).obj G,
      v ≫ Mod.extendUnitHom a M ≫ q.hom =
        w ≫ (Mod.freeForgetAdjunction D).unit.app G := by
  obtain ⟨t, ht, _⟩ := AlgebraicGeometry.ProEtale.spFreeTensor_linear p a r ha (𝟙 G)
  let g := f ≫ t
  let q := Mod.extendHom a g
  refine ⟨q, ?_⟩
  change v ≫ Mod.extendUnitHom a M ≫ (Mod.extendHom a (f ≫ t)).hom = _
  rw [Mod.extendUnitHom_extendHom]
  change v ≫ (f.hom ≫ t.hom) = _
  rw [← Category.assoc, hf, Category.assoc, ht, freeUnit_tensorMap, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem quotientRootProjection_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (roots : IntegralRoots l E X) :
    ∃ q : quotientLine l E π n X ⟶
        (Mod.free (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).obj
            (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))),
      roots.hom ≫ quotientLineMap l E π n X ≫ q.hom =
        limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
          (Mod.freeForgetAdjunction (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).unit.app
              (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  unfold quotientLine quotientLineMap
  let I := (Ideal.span {π}) ^ (n + 1)
  have hle : spTateEllIdeal l E n ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h : ((l ^ (n + 1) : ℕ) : completedResidue l E π n) = 0 := by
      let d : ULift.{u + 1} (completedResidue l E π n) →+*
          completedResidue l E π n := ULift.ringEquiv.toRingHom
      exact (map_natCast d _).symm.trans ((congrArg d hA).trans (map_zero d))
    rw [← Nat.cast_pow]
    exact (map_natCast (Ideal.Quotient.mk I) _).trans h
  let a : spEllQuotient l E n →+* completedResidue l E π n := Ideal.Quotient.factor hle
  let : TopologicalSpace (spEllQuotient l E n) := ⊥
  let : DiscreteTopology (spEllQuotient l E n) := ⟨rfl⟩
  let : IsTopologicalRing (spEllQuotient l E n) := DiscreteTopology.topologicalRing
  let aP : spEllPointRingObj.{u} l E n ⟶
      Profinite.continuousMapRingObj.{u} (completedResidue l E π n) :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap a continuous_of_discreteTopology)
  have : IsMonHom aP := by dsimp only [aP]; infer_instance
  have haP : spEllPointReduction.{u} l E n ≫ aP = quotientMap l E π n := by
    unfold spEllPointReduction quotientMap completedReduction
    dsimp only [aP]
    rw [← Functor.map_comp]
    rfl
  let aX := coefficientMap aP X
  have haX : spEllReduction X l E n ≫ aX =
      coefficientMap (quotientMap l E π n) X := by
    rw [← coefficientMap_comp, haP]
  let f : spIntegralTwist X l E ⟶
      (Mod.comap (spEllReduction X l E n)).obj
        ((Mod.free (condensedRingObj (spEllPointRingObj l E n) X)).obj
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) := by
    unfold spIntegralTwist
    exact limit.π (spIntegralTwistSystem X l E) (op n)
  exact extendFreeProjection (spEllReduction X l E n)
    (coefficientMap (quotientMap l E π n) X) aX haX (spIntegralTwist X l E)
    (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))
    f roots.hom
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    (by exact roots.projections n)

/-- The quotient of the integral root line has the prescribed finite root endpoint.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), expected reductions;
Stacks Tags 0990, 090K, 03EK and 03EL, as expanded in
lem-amb-tate-root-projection-reduction.
(blueprint: lem-diagonal-quotient-root-endpoint).

Proof in words. Construct the integral root map with its projection equations.
Annihilation of the quotient by l^(n+1) factors its coefficient map through the
n-th ell-power quotient. Tensor this factor with the identity on the n-th roots,
compose with the integral limit projection, and transpose under scalar extension.
The free-module unit equation gives its exact root normalization. The resulting
map is invertible by the epic local rank-one argument of
lem-diagonal-quotient-root-projection-iso. The free-module adjunction transports
through the supplied equivalence and underlying-sheaf comparison. The pulled-back
finite Cartier line represents the same root maps, by its etale free-module
universal property and the comparison adjunction. Their representing isomorphism
preserves the root units. Compose it with the realized quotient projection and
use naturality of the underlying comparison to obtain the required equation.
Package this endpoint with the integral map and the supplied finite roots.
No flatness, ramification-index divisibility, or choice of realization is used. -/
theorem diagonalQuotientRootEndpoint
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsUnit (l : Γ(X, ⊤)))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    [Finite (ULift.{u + 1} (completedResidue l E π n))]
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) X)
    (finiteRoots : FiniteRoots X (l ^ (n + 1))) :
    Nonempty (QuotientLineRealization l E π n n hA X e) := by
  have _ := hπ
  let roots := diagonalIntegralRoots l X E
  obtain ⟨q, hq⟩ := quotientRootProjection_exists l X E π n hA roots
  have : IsIso q := diagonalQuotientRootProjection_isIso l X hX E π n hA roots q hq
  obtain ⟨endpoint⟩ := endpointFromFree e (l ^ (n + 1)) hA finiteRoots q
    (roots.hom ≫ quotientLineMap l E π n X)
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    (by simpa only [Category.assoc] using hq)
  unfold QuotientLineRealization
  exact ⟨roots, finiteRoots, endpoint⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
