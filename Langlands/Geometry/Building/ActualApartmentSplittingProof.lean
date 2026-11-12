import Langlands.Geometry.Building.ActualApartmentSplittingStatement
import Langlands.GroupScheme.Derived.CentralSplitTorusFactorization
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusAssembly
import Langlands.Geometry.Building.DerivedTranslation

/-! # Proof: the actual apartment splitting of KP Axiom 4.1.4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme

section Center

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Conjugation by a central base point is the identity. -/
theorem innerIso_hom_eq_id_of_mem_center {n : Over.mk (𝟙 S) ⟶ G.X}
    (hn : n ∈ (center G).carrier (Over.mk (𝟙 S))) : (G.innerIso n).hom = 𝟙 G := by
  apply hom_ext_points
  intro U x
  rw [comp_innerIso_hom]
  have hc : Commute (G.constantPoint n U) x := hn U (Over.homMk U.hom (by simp)) x
  rw [hc.eq, mul_inv_cancel_right]
  rfl

end Center

section DerivedTorus

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {S S_D : CommGroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {i : S.toGrp ⟶ G} {j : S_D.toGrp ⟶ D} {e : S_D ⟶ S}

/-- A homomorphism from the derived maximal split torus to `S` whose composite with `i` takes
values in the derived subgroup factors through `e`. -/
theorem IsDerivedSubgroup.exists_factor_derivedTorus
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (q : S_D ⟶ S)
    (hq : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S_D.X),
      x ≫ (CommGroupScheme.groupHom q ≫ i).hom.hom ∈ (derivedSubgroup G).carrier U) :
    ∃ f : S_D ⟶ S_D, f ≫ e = q := by
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  have hqr : SubgroupFunctor.range (CommGroupScheme.groupHom q ≫ i) ≤
      derivedSubgroup G := by
    rintro U _ ⟨x, rfl⟩
    exact hq U x
  let b : S_D.toGrp ⟶ D := hd.isRepresentedBy.factorHom
    (CommGroupScheme.groupHom q ≫ i) hqr
  have hb : b ≫ d = CommGroupScheme.groupHom q ≫ i :=
    hd.isRepresentedBy.factorHom_comp _ _
  have hbj : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S_D.X)
      (y : U ⟶ S_D.X), Commute (x ≫ b.hom.hom) (y ≫ j.hom.hom) := by
    intro U x y
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono d.hom.hom).mp
    have hbx : (x ≫ b.hom.hom) ≫ d.hom.hom =
        (x ≫ (CommGroupScheme.groupHom q).hom.hom) ≫ i.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => x ≫ z.hom.hom) hb
    have hjy : (y ≫ j.hom.hom) ≫ d.hom.hom =
        (y ≫ (CommGroupScheme.groupHom e).hom.hom) ≫ i.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun z => y ≫ z.hom.hom) he
    rw [MonObj.mul_comp, MonObj.mul_comp, hbx, hjy,
      ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  obtain ⟨f, hf⟩ := hj.exists_factor_of_commute hj.1.1 b hbj
  refine ⟨Additive.ofMul f, ?_⟩
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  have hcomp : (f ≫ CommGroupScheme.groupHom e) ≫ i =
      CommGroupScheme.groupHom q ≫ i := by
    rw [Category.assoc, ← he, ← Category.assoc, hf, hb]
  exact congrArg (fun z => z.hom.hom) hcomp

omit [IsAffineHom G.X.hom] in
/-- The derived torus composite twisted by a normalizing point takes values in the
derived subgroup. -/
theorem IsDerivedSubgroup.normalizing_mem_derivedSubgroup
    (hd : IsDerivedSubgroup d) (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} {σ : S ≅ S}
    (hn : IsNormalizingPoint i n σ)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ S_D.X) :
    x ≫ (CommGroupScheme.groupHom (e ≫ σ.hom) ≫ i).hom.hom ∈
      (derivedSubgroup G).carrier U := by
  have h1 : CommGroupScheme.groupHom (e ≫ σ.hom) ≫ i = (j ≫ d) ≫ (G.innerIso n).hom := by
    change CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom σ.hom ≫ i = _
    rw [← hn, ← Category.assoc, ← he]
  have hmem : x ≫ (j ≫ d).hom.hom ∈ (derivedSubgroup G).carrier U := by
    rw [← hd.2]
    exact SubgroupFunctor.mem_range.mpr
      ⟨x ≫ j.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
  rw [h1, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  exact derivedSubgroup_isNormal G U _ _ trivial hmem

/-- A normalizing point of `S` preserves the derived maximal split torus inside `S`. -/
theorem IsDerivedSubgroup.exists_derivedTorus_iso
    (hd : IsDerivedSubgroup d) (hi : IsSplitSubtorus i)
    (hj : IsMaximalSplitTorus j)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hec : IsClosedSubgroup (CommGroupScheme.groupHom e))
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} {σ : S ≅ S}
    (hn : IsNormalizingPoint i n σ) :
    ∃ τ : S_D ≅ S_D, τ.hom ≫ e = e ≫ σ.hom := by
  have : IsClosedImmersion (CommGroupScheme.groupHom e).hom.hom.left := hec
  have : Mono (CommGroupScheme.groupHom e).hom.hom := Over.mono_of_mono_left _
  have hcancel : ∀ g₁ g₂ : S_D ⟶ S_D, g₁ ≫ e = g₂ ≫ e → g₁ = g₂ := by
    intro g₁ g₂ h
    apply CommGroupScheme.hom_ext_points
    intro U x
    apply (cancel_mono (CommGroupScheme.groupHom e).hom.hom).mp
    have := congrArg (fun z => x ≫ (CommGroupScheme.groupHom z).hom.hom) h
    simpa only [comp_groupHom_comp] using this
  obtain ⟨f, hf⟩ := hd.exists_factor_derivedTorus hi hj he (e ≫ σ.hom)
    (hd.normalizing_mem_derivedSubgroup he hn)
  obtain ⟨f', hf'⟩ := hd.exists_factor_derivedTorus hi hj he (e ≫ σ.symm.hom)
    (hd.normalizing_mem_derivedSubgroup he hn.inv)
  refine ⟨⟨f, f', hcancel _ _ ?_, hcancel _ _ ?_⟩, hf⟩
  · rw [Category.assoc, hf', ← Category.assoc, hf, Category.assoc, Iso.symm_hom,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hf, ← Category.assoc, hf', Category.assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

end DerivedTorus

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- A normalizer point lying in the centre of `G` acts trivially on the apartment
(KP Axiom 4.1.4 (A 1), last sentence). -/
theorem normalizerAction_eq_one_of_mem_center (n : normalizerPoints B.i)
    (hn : (n : rationalPoints G) ∈ (center G).carrier (Over.mk (𝟙 _))) :
    B.normalizerAction n = 1 := by
  have hninv : ((n⁻¹ : normalizerPoints B.i) : rationalPoints G) ∈
      (center G).carrier (Over.mk (𝟙 _)) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hn
  have hrefl : IsNormalizingPoint B.i ((n⁻¹ : normalizerPoints B.i) : rationalPoints G)
      (Iso.refl B.S) := by
    rw [isNormalizingPoint_refl_iff, innerIso_hom_eq_id_of_mem_center hninv]
    exact Category.comp_id _
  have hw : ∀ a, weylAction B.i n⁻¹ a = a := fun a => by
    rw [weylAction_eq B.i hrefl a]
    exact Category.id_comp a
  have hcent : (n : rationalPoints G) ∈ Subgroup.center (rationalPoints G) :=
    center_carrier_le_center G hn
  apply AffineEquiv.ext
  intro x
  rw [normalizerAction_apply]
  change n • x = x
  apply KPApartmentData.Apartment.ext
  rw [KPApartmentData.val_smul]
  ext a g
  rw [RootFunctionFamily.smul_apply, hw a, mul_assoc, Subgroup.mem_center_iff.mp hcent g,
    inv_mul_cancel_left]

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.Geometry.Building

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.GroupScheme.RealTorusSpace

section Complement

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {T A S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The images of the two factors of a central isogeny `T × A → S` of split tori are
complementary subspaces of `V(S)`. -/
theorem isCompl_cocharacterRange_of_isCentralIsogeny
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp) (hS : IsSplitTorus S.toGrp)
    (e : T ⟶ S) (c : A ⟶ S)
    (hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c)) :
    IsCompl (LinearMap.range (cocharacterMapReal e))
      (LinearMap.range (cocharacterMapReal c)) := by
  have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.flat
  have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.surjective
  refine ⟨?_, codisjoint_iff.mpr
    (cocharacterRange_sup_eq_top_of_centralComplement e c hT hA hS)⟩
  let P : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := T.toGrp ⊗ A.toGrp
      comm := (hT.tensor hA).isCommMonObj }
  let p : P ⟶ S := Additive.ofMul (RelativeRoot.centralComplementProduct e c)
  let q : P ⟶ T := Additive.ofMul (RelativeRoot.centralComplementProduct (𝟙 T) (0 : A ⟶ T))
  let inl : T ⟶ P := Additive.ofMul (prodInl T.toGrp A.toGrp)
  let inr : A ⟶ P := Additive.ofMul (prodInr T.toGrp A.toGrp)
  have hinl : ∀ {Z : CommGroupScheme (Spec (CommRingCat.of k))} (f : T ⟶ Z) (g : A ⟶ Z),
      inl ≫ (Additive.ofMul (RelativeRoot.centralComplementProduct f g) : P ⟶ Z) = f := by
    intro Z f g
    apply CommGroupScheme.hom_ext_points
    intro U x
    rw [comp_groupHom_comp]
    change (x ≫ (prodInl T.toGrp A.toGrp).hom.hom) ≫
      (RelativeRoot.centralComplementProduct f g).hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, prodInl_prodHom]
  have hinr : ∀ {Z : CommGroupScheme (Spec (CommRingCat.of k))} (f : T ⟶ Z) (g : A ⟶ Z),
      inr ≫ (Additive.ofMul (RelativeRoot.centralComplementProduct f g) : P ⟶ Z) = g := by
    intro Z f g
    apply CommGroupScheme.hom_ext_points
    intro U x
    rw [comp_groupHom_comp]
    change (x ≫ (prodInr T.toGrp A.toGrp).hom.hom) ≫
      (RelativeRoot.centralComplementProduct f g).hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, prodInr_prodHom]
  have : IsFinite (CommGroupScheme.groupHom p).hom.hom.left := hp.isFinite
  have hpinj : Function.Injective (cocharacterMapReal p) := by
    simpa only [cocharacterMapReal, LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
        (cocharacterMapInt p) (cocharacterMapInt_injective_of_isFinite p)
  have hid : cocharacterMapReal (𝟙 T) = LinearMap.id := by
    have h : cocharacterMapInt (𝟙 T) = LinearMap.id := by
      ext ν
      exact Category.comp_id ν
    unfold cocharacterMapReal
    rw [h, LinearMap.baseChange_id]
  have hzero : cocharacterMapReal (0 : A ⟶ T) = 0 := by
    have h : cocharacterMapInt (0 : A ⟶ T) = 0 := by
      ext ν
      change ν ≫ (0 : A ⟶ T) = 0
      exact Limits.comp_zero
    unfold cocharacterMapReal
    rw [h, LinearMap.baseChange_zero]
  rw [Submodule.disjoint_def]
  rintro v ⟨w, rfl⟩ ⟨z, hz⟩
  have h0 : cocharacterMapReal inl w = cocharacterMapReal inr z := by
    apply hpinj
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← cocharacterMapReal_comp,
      ← cocharacterMapReal_comp, hinl, hinr, hz]
  have h1 := congrArg (cocharacterMapReal q) h0
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← cocharacterMapReal_comp,
    ← cocharacterMapReal_comp, hinl, hinr, hid, hzero, LinearMap.id_apply,
    LinearMap.zero_apply] at h1
  rw [h1, map_zero]

end Complement

/-- **KP Axiom 4.1.4 for actual data.** Every actual valuation-building datum carries an
actual apartment splitting: the derived subgroup, a maximal split torus of it inside `S` and
the split component of `G`. The Chapter 7 apartment axioms are not used. -/
theorem actualApartmentSplitting : ActualApartmentSplittingStatement.{u} := by
  intro F _ _ _ _ G _ B _
  have hG := B.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨S_D, j, e, hj, he, hje⟩ :=
    derivedMaximalSplitTorus F G D d hG hd B.S B.i B.isMaximalSplitTorus
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement F G hG
  obtain ⟨g, hg⟩ := B.isMaximalSplitTorus.exists_factor_of_commute ha.1.1.1 a
    (fun U x y => commute_of_mem_center (ha.1.2 U x) _)
  let c : A ⟶ B.S := Additive.ofMul g
  have hc : CommGroupScheme.groupHom c ≫ B.i = a := hg
  have hcis : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c) :=
    derivedCentralSplitTorusProduct F G D d hG hd B.S S_D A B.i j e a c
      B.isMaximalSplitTorus hj he hje ha hc
  refine ⟨{ D := D, d := d, derivedTorus := S_D, j := j, e := e, centralTorus := A, a := c },
    ?_⟩
  exact
    { isDerivedSubgroup := hd
      isMaximalSplitTorus_j := hj
      isClosedSubgroup_e := he
      j_comp_d := hje
      isSplitComponent := by
        change IsSplitComponent (CommGroupScheme.groupHom c ≫ B.i)
        rw [hc]
        exact ha
      isCompl := isCompl_cocharacterRange_of_isCentralIsogeny hj.1.1 ha.1.1.1
        B.isMaximalSplitTorus.1.1 e c hcis
      normalizer_derivedTorus := fun n =>
        hd.exists_derivedTorus_iso B.isMaximalSplitTorus.1 hj hje he
          (isNormalizingPoint_normalizingAut B.i n)
      center_acts_trivially := fun n hn => B.normalizerAction_eq_one_of_mem_center n hn
      affineConjugations := B.hasAffineConjugations }

end Langlands.Geometry.Building
