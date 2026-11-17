import Langlands.GroupScheme.Reductive.SimpleFactorPoints
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductFactors
import Langlands.GroupScheme.CentralIsogeny.PerfectComposition
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Reductive.Noncommutativity
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.SimplyConnected.DirectFactors

/-! # A central isogeny onto a semisimple group from a product of almost-simple groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SimpleFactor

section Base

variable {S : Scheme.{u}}

/-- The product of two central isogenies is a central isogeny. -/
theorem IsCentralIsogeny.tensorHom {C H C' H' : GroupScheme S} {f : C ⟶ H} {g : C' ⟶ H'}
    (hf : IsCentralIsogeny f) (hg : IsCentralIsogeny g) : IsCentralIsogeny (f ⊗ₘ g) := by
  have h1 := IsCentralIsogeny.tensor_id hf C'
  have h2 := IsCentralIsogeny.id_tensor hg H
  have hdec : f ⊗ₘ g = (f ⊗ₘ 𝟙 C') ≫ (𝟙 H ⊗ₘ g) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have : LocallyOfFinitePresentation (f ⊗ₘ 𝟙 C').hom.hom.left :=
    h1.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation (𝟙 H ⊗ₘ g).hom.hom.left :=
    h2.locallyOfFinitePresentation
  refine ⟨?_, ?_, ?_⟩
  · rw [hdec]
    exact h1.isIsogeny.comp h2.isIsogeny
  · rw [hdec]
    change LocallyOfFinitePresentation
      ((f ⊗ₘ 𝟙 C').hom.hom.left ≫ (𝟙 H ⊗ₘ g).hom.hom.left)
    infer_instance
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  change x ≫ (f.hom.hom ⊗ₘ g.hom.hom) = 1 at hx
  have hxC : (x ≫ fst C.X C'.X) ≫ f.hom.hom = 1 := by
    have h := congrArg (fun w => w ≫ fst H.X H'.X) hx
    simpa only [Category.assoc, tensorHom_fst, MonObj.one_comp] using h
  have hxC' : (x ≫ snd C.X C'.X) ≫ g.hom.hom = 1 := by
    have h := congrArg (fun w => w ≫ snd H.X H'.X) hx
    simpa only [Category.assoc, tensorHom_snd, MonObj.one_comp] using h
  intro T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (hf.mem_center_of_comp_eq_one hxC T' a (y ≫ fst C.X C'.X)).eq
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (hg.mem_center_of_comp_eq_one hxC' T' a (y ≫ snd C.X C'.X)).eq

section CommutingMultiplication

variable {H K G P : GroupScheme S} (j : H ⟶ G) (i : K ⟶ G)
  (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
    Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- The commuting multiplication restricted to the first factor is the first inclusion. -/
theorem lift_zero_comp_commutingSubgroupMultiplicationHom (p : P ⟶ H) :
    lift p 0 ≫ commutingSubgroupMultiplicationHom j i hc = p ≫ j := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_commutingSubgroupMultiplicationHom,
    Grp.comp_hom_hom]
  simp only [Grp.lift_hom, Mon.lift_hom, Category.assoc, lift_fst, lift_snd]
  change (x ≫ p.hom.hom ≫ j.hom.hom) * (x ≫ (1 : P.X ⟶ K.X) ≫ i.hom.hom) = _
  rw [MonObj.one_comp, MonObj.comp_one, mul_one]

/-- The commuting multiplication restricted to the second factor is the second inclusion. -/
theorem lift_zero_left_comp_commutingSubgroupMultiplicationHom (q : P ⟶ K) :
    lift 0 q ≫ commutingSubgroupMultiplicationHom j i hc = q ≫ i := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_commutingSubgroupMultiplicationHom,
    Grp.comp_hom_hom]
  simp only [Grp.lift_hom, Mon.lift_hom, Category.assoc, lift_fst, lift_snd]
  change (x ≫ (1 : P.X ⟶ H.X) ≫ j.hom.hom) * (x ≫ q.hom.hom ≫ i.hom.hom) = _
  rw [MonObj.one_comp, MonObj.comp_one, one_mul]

end CommutingMultiplication

section Sum

variable {I J : Type u} [Finite I] [Finite J] (A : I → GroupScheme S) (B : J → GroupScheme S)

/-- The first component of the inverse of the disjoint-union product comparison. -/
theorem finiteProductSumIso_inv_fst :
    (finiteProductSumIso A B).inv ≫ fst (pi A) (pi B) =
      Pi.lift (f := A) (fun i => Pi.π (sumGroupFamily A B) (Sum.inl i)) :=
  lift_fst _ _

/-- The second component of the inverse of the disjoint-union product comparison. -/
theorem finiteProductSumIso_inv_snd :
    (finiteProductSumIso A B).inv ≫ snd (pi A) (pi B) =
      Pi.lift (f := B) (fun j => Pi.π (sumGroupFamily A B) (Sum.inr j)) :=
  lift_snd _ _

/-- A left coordinate of the product over a disjoint union, read in the binary product. -/
theorem piFactorInclusionHom_inl_comp_finiteProductSumIso_inv (a : I) :
    piFactorInclusionHom (sumGroupFamily A B) (Sum.inl a) ≫ (finiteProductSumIso A B).inv =
      piFactorInclusionHom A a ≫ lift (𝟙 (pi A)) 0 := by
  classical
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, lift_fst, Category.comp_id]
    rw [finiteProductSumIso_inv_fst]
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π]
    by_cases h : a = i
    · subst h
      rw [piFactorInclusionHom_π_self, piFactorInclusionHom_π_self]
    · rw [piFactorInclusionHom_π_ne _ _ _ (fun h' => h (Sum.inl_injective h')),
        piFactorInclusionHom_π_ne _ _ _ h]
  · rw [Category.assoc, Category.assoc, lift_snd, comp_zero]
    rw [finiteProductSumIso_inv_snd]
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.lift_comp_π, zero_comp,
      piFactorInclusionHom_π_ne _ _ _ Sum.inl_ne_inr]
    rfl

/-- A right coordinate of the product over a disjoint union, read in the binary product. -/
theorem piFactorInclusionHom_inr_comp_finiteProductSumIso_inv (b : J) :
    piFactorInclusionHom (sumGroupFamily A B) (Sum.inr b) ≫ (finiteProductSumIso A B).inv =
      piFactorInclusionHom B b ≫ lift 0 (𝟙 (pi B)) := by
  classical
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, lift_fst, comp_zero]
    rw [finiteProductSumIso_inv_fst]
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, zero_comp,
      piFactorInclusionHom_π_ne _ _ _ Sum.inr_ne_inl]
    rfl
  · rw [Category.assoc, Category.assoc, lift_snd, Category.comp_id]
    rw [finiteProductSumIso_inv_snd]
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.lift_comp_π]
    by_cases h : b = j
    · subst h
      rw [piFactorInclusionHom_π_self, piFactorInclusionHom_π_self]
    · rw [piFactorInclusionHom_π_ne _ _ _ (fun h' => h (Sum.inr_injective h')),
        piFactorInclusionHom_π_ne _ _ _ h]

end Sum

end Base

variable {k : Type u} [Field k]

/-- The existence statement proved by Lie-dimension induction, without normality. -/
theorem exists_almostSimplePresentation_aux (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G) :
    ∃ (I : Type u) (_ : Finite I) (A : I → GroupScheme (Spec (CommRingCat.of k)))
      (mul : pi A ⟶ G), (∀ i, IsAlmostSimple (A i)) ∧
      (∀ i, IsClosedSubgroup (piFactorInclusionHom A i ≫ mul)) ∧ IsCentralIsogeny mul := by
  classical
  let P : GroupScheme (Spec (CommRingCat.of k)) → Prop := fun G =>
    IsSemisimple G → ∃ (I : Type u) (_ : Finite I)
      (A : I → GroupScheme (Spec (CommRingCat.of k))) (mul : pi A ⟶ G),
      (∀ i, IsAlmostSimple (A i)) ∧
      (∀ i, IsClosedSubgroup (piFactorInclusionHom A i ≫ mul)) ∧ IsCentralIsogeny mul
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  have : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  suffices h : P G from h hG
  apply smoothConnectedAffineGroup_lieDimension_induction P ?_ G
  intro G _ _ _ ih hG
  by_cases htriv : SubgroupFunctor.range (𝟙 G) = ⊥
  · let D := SimplyConnectedAlmostSimpleProduct.empty (G := G) htriv
    exact ⟨D.Index, D.finite, D.factor, D.iso.inv, fun i => i.elim, fun i => i.elim,
      isCentralIsogeny_of_isIso _⟩
  by_cases hAS : IsAlmostSimple G
  · have : IsIso (Pi.π (fun _ : PUnit.{u + 1} => G) PUnit.unit) :=
      (productUniqueIso (fun _ : PUnit.{u + 1} => G)).isIso_hom
    refine ⟨PUnit.{u + 1}, inferInstance, fun _ => G,
      Pi.π (fun _ : PUnit.{u + 1} => G) PUnit.unit, fun _ => hAS, ?_,
      isCentralIsogeny_of_isIso _⟩
    rintro ⟨⟩
    rw [piFactorInclusionHom_π_self]
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  have hbad : ¬ ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range j).IsNormal →
      SubgroupFunctor.range j = ⊥ ∨ SubgroupFunctor.range j = ⊤ := by
    intro h
    exact hAS ⟨hG, hG.noncommutative_of_nontrivial htriv, h⟩
  push Not at hbad
  obtain ⟨H, j, hj, hsH, hcH, hnH, hntH, hfullH⟩ := hbad
  obtain ⟨hH, K, i, hK, hi, _, _, hc, hm⟩ :=
    semisimpleNormalIsogenyComplement k G H hG j hj hsH hcH hnH
  have : Smooth H.X.hom := hsH
  have : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  have : ConnectedSpace H.X.left := hcH
  have : Smooth K.X.hom := hK.isConnectedReductive.smooth
  have : IsAffineHom K.X.hom := hK.isConnectedReductive.isAffineHom
  have : ConnectedSpace K.X.left := hK.isConnectedReductive.connectedSpace
  have hjproper : ¬ IsIso j := by
    intro hjiso
    have hrep : SubgroupFunctor.range j = ⊤ := by
      apply SubgroupFunctor.ext
      intro T
      apply top_unique
      intro x _
      have : IsIso j.hom.hom := (Grp.forget _).map_isIso j
      refine ⟨x ≫ inv j.hom.hom, ?_⟩
      change (x ≫ inv j.hom.hom) ≫ j.hom.hom = x
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hfullH hrep
  have hiproper : ¬ IsIso i := by
    intro hiiso
    apply hntH
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : IsIso i.hom.hom := (Grp.forget _).map_isIso i
    have hcommH : ∀ (U : Over (Spec (CommRingCat.of k))) (x y : U ⟶ H.X), Commute x y := by
      intro U x y
      have h1 := hc U x ((y ≫ j.hom.hom) ≫ inv i.hom.hom)
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h1
      show x * y = y * x
      apply (cancel_mono j.hom.hom).mp
      rw [MonObj.mul_comp, MonObj.mul_comp]
      exact h1.eq
    have htrivH : SubgroupFunctor.range (𝟙 H) = ⊥ := by
      by_contra hne
      exact hH.noncommutative_of_nontrivial hne hcommH
    apply SubgroupFunctor.ext
    intro T
    rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    have hh1 : h = 1 := by
      have hh : h ∈ (SubgroupFunctor.range (𝟙 H)).carrier T := ⟨h, Category.comp_id h⟩
      simpa only [htrivH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hh
    rw [hh1, MonObj.one_comp]
  obtain ⟨I₁, _, A₁, mul₁, has₁, hcl₁, hci₁⟩ :=
    ih H (Lie.dimension_lt_of_proper_closedSubgroup j hj hjproper) hH
  obtain ⟨I₂, _, A₂, mul₂, has₂, hcl₂, hci₂⟩ :=
    ih K (Lie.dimension_lt_of_proper_closedSubgroup i hi hiproper) hK
  let m := commutingSubgroupMultiplicationHom j i hc
  refine ⟨I₁ ⊕ I₂, inferInstance, sumGroupFamily A₁ A₂,
    (finiteProductSumIso A₁ A₂).inv ≫ (mul₁ ⊗ₘ mul₂) ≫ m, ?_, ?_, ?_⟩
  · rintro (a | b)
    · exact has₁ a
    · exact has₂ b
  · rintro (a | b)
    · have key : piFactorInclusionHom (sumGroupFamily A₁ A₂) (Sum.inl a) ≫
          (finiteProductSumIso A₁ A₂).inv ≫ (mul₁ ⊗ₘ mul₂) ≫ m =
          (piFactorInclusionHom A₁ a ≫ mul₁) ≫ j := by
        rw [← Category.assoc, piFactorInclusionHom_inl_comp_finiteProductSumIso_inv,
          Category.assoc, ← Category.assoc (lift _ _), lift_map, Category.id_comp, zero_comp,
          lift_zero_comp_commutingSubgroupMultiplicationHom, Category.assoc]
      rw [key]
      have : IsClosedImmersion (piFactorInclusionHom A₁ a ≫ mul₁).hom.hom.left := hcl₁ a
      have : IsClosedImmersion j.hom.hom.left := hj
      change IsClosedImmersion
        ((piFactorInclusionHom A₁ a ≫ mul₁).hom.hom.left ≫ j.hom.hom.left)
      infer_instance
    · have key : piFactorInclusionHom (sumGroupFamily A₁ A₂) (Sum.inr b) ≫
          (finiteProductSumIso A₁ A₂).inv ≫ (mul₁ ⊗ₘ mul₂) ≫ m =
          (piFactorInclusionHom A₂ b ≫ mul₂) ≫ i := by
        rw [← Category.assoc, piFactorInclusionHom_inr_comp_finiteProductSumIso_inv,
          Category.assoc, ← Category.assoc (lift _ _), lift_map, Category.id_comp, zero_comp,
          lift_zero_left_comp_commutingSubgroupMultiplicationHom, Category.assoc]
      rw [key]
      have : IsClosedImmersion (piFactorInclusionHom A₂ b ≫ mul₂).hom.hom.left := hcl₂ b
      have : IsClosedImmersion i.hom.hom.left := hi
      change IsClosedImmersion
        ((piFactorInclusionHom A₂ b ≫ mul₂).hom.hom.left ≫ i.hom.hom.left)
      infer_instance
  · have h1 : IsCentralIsogeny ((finiteProductSumIso A₁ A₂).inv ≫ (mul₁ ⊗ₘ mul₂)) :=
      (IsCentralIsogeny.tensorHom hci₁ hci₂).iso_comp (finiteProductSumIso A₁ A₂).symm
    have hperf : derivedSubgroup (pi (sumGroupFamily A₁ A₂)) = ⊤ := by
      apply derivedSubgroup_pi_eq_top
      rintro (a | b)
      · exact semisimplePerfect k _ (has₁ a).isSemisimple
      · exact semisimplePerfect k _ (has₂ b).isSemisimple
    have h2 := IsCentralIsogeny.comp_of_derivedSubgroup_eq_top hperf h1 hm
    simpa only [Category.assoc] using h2

/-- **Almost-simple central product presentation.** A semisimple group `G` over a field
receives a central isogeny `mul : ∏ A i ⟶ G` from a finite product of almost-simple groups,
each of whose factor inclusions `A i ⟶ G` is a closed immersion with normal range. -/
theorem exists_almostSimplePresentation (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G) :
    ∃ (I : Type u) (_ : Finite I) (A : I → GroupScheme (Spec (CommRingCat.of k)))
      (mul : pi A ⟶ G), (∀ i, IsAlmostSimple (A i)) ∧
      (∀ i, IsClosedSubgroup (piFactorInclusionHom A i ≫ mul)) ∧
      (∀ i, (SubgroupFunctor.range (piFactorInclusionHom A i ≫ mul)).IsNormal) ∧
      IsCentralIsogeny mul := by
  obtain ⟨I, _, A, mul, has, hcl, hci⟩ := exists_almostSimplePresentation_aux G hG
  refine ⟨I, inferInstance, A, mul, has, hcl, ?_, hci⟩
  intro i
  have : IsFinite mul.hom.hom.left := hci.isFinite
  have : QuasiCompact (𝟙 (A i) : A i ⟶ A i).hom.hom.left := by
    change QuasiCompact (𝟙 (A i).X.left)
    infer_instance
  have : Flat (𝟙 (A i) : A i ⟶ A i).hom.hom.left := by
    change Flat (𝟙 (A i).X.left)
    infer_instance
  have : Surjective (𝟙 (A i) : A i ⟶ A i).hom.hom.left := by
    change Surjective (𝟙 (A i).X.left)
    infer_instance
  have : Flat mul.hom.hom.left := hci.flat
  have : Surjective mul.hom.hom.left := hci.surjective
  have : IsClosedImmersion (piFactorInclusionHom A i ≫ mul).hom.hom.left := hcl i
  have : Mono (piFactorInclusionHom A i ≫ mul).hom.hom := Over.mono_of_mono_left _
  exact isNormal_range_of_image mul (𝟙 (A i)) (piFactorInclusionHom A i)
    (isNormal_range_piFactorInclusionHom A i) (piFactorInclusionHom A i ≫ mul)
    (Category.id_comp _)

end Langlands.GroupScheme.SimpleFactor
