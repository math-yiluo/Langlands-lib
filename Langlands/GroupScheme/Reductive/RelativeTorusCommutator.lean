import Langlands.GroupScheme.Reductive.RelativeCorootCommutator
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Reductive.RelativeDerivedReduction
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity

/-! # Finite coroot index and fppf-local torus commutators -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Local abstract commutators form a subgroup functor on the original group. -/
def locallyCommutatorFunctor (G : GroupScheme S) : SubgroupFunctor G where
  carrier := locallyCommutatorSubgroup
  comp_mem := fun a _ hx => LocallyCommutator.restrict hx a

/-- A positive multiple of a cocharacter landing in local commutators implies
the same for the original cocharacter. -/
theorem cocharactersLandingIn_locallyCommutator_of_nsmul
    {D : CommGroupScheme S} (i : D.toGrp ⟶ G) (ν : cocharacterLattice D)
    (n : ℕ) (hn : n ≠ 0)
    (hν : (n : ℤ) • ν ∈ cocharactersLandingIn i (locallyCommutatorFunctor G)) :
    ν ∈ cocharactersLandingIn i (locallyCommutatorFunctor G) := by
  intro Z t
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
    Z.left.affineCover.changeProp (fun j => by
      have := Z.left.affineCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro j
  let V : Over S := Over.mk (𝒰.f j ≫ Z.hom)
  let a : V ⟶ Z := Over.homMk (𝒰.f j) rfl
  have : IsAffine V.left := inferInstanceAs (IsAffine (Z.left.affineCover.X j))
  obtain ⟨W, b, hW, hflat, hsurj, hfp, r, hr⟩ :=
    UnitPowerExtension.exists_roots_test V n hn (fun _ : Fin 1 => Gm.pointsEquiv S V (a ≫ t))
  let : Flat b.left := hflat
  let : Surjective b.left := hsurj
  let : LocallyOfFinitePresentation b.left := hfp
  let z : W ⟶ (Gm S).X := (Gm.pointsEquiv S W).symm (r 0)
  have hz : z ^ n = b ≫ (a ≫ t) := by
    apply (Gm.pointsEquiv S W).injective
    rw [map_pow, MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
    exact hr 0
  apply LocallyCommutator.of_surjective b
  have hm := hν W z
  change LocallyCommutator (z ≫ (CommGroupScheme.groupHom ((n : ℤ) • ν) ≫ i).hom.hom) at hm
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul, zpow_natCast,
    ← MonObj.pow_comp, hz] at hm
  simpa only [Grp.comp_hom_hom, Category.assoc] using hm

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.splitTorus

variable (S : Scheme.{u}) (I : Type u) [Fintype I]

/-- Fixed integral coordinate cocharacters depend linearly on the exponent vector. -/
def exponentCocharacterLinear : (I → ℤ) →ₗ[ℤ] cocharacterLattice (commGroupScheme S I) where
  toFun := exponentCocharacter S I
  map_add' m n := by
    simp only [exponentCocharacter, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c m := by
    simp only [exponentCocharacter, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
      smul_smul, RingHom.id_apply]

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme.RelativeDerived

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Finite coroot index makes every fixed-coordinate cocharacter locally
an abstract commutator, because local membership is saturated under positive multiples. -/
theorem exponentCocharacter_mem_locallyCommutator_of_finiteIndex (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hindex : ∀ v : I → ℤ, ∃ n : ℕ, 0 < n ∧ (n : ℤ) • v ∈ P.corootSpan ℤ)
    (v : I → ℤ) :
    splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I v ∈
      cocharactersLandingIn i (locallyCommutatorFunctor G) := by
  let e := splitTorus.exponentCocharacterLinear (Spec (CommRingCat.of R)) I
  let M := (cocharactersLandingIn i (locallyCommutatorFunctor G)).comap e
  have hle : P.corootSpan ℤ ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    intro Z t
    change LocallyCommutator
      (t ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (P.coroot a)) ≫ i).hom.hom)
    rw [Grp.comp_hom_hom]
    exact locallyCommutator_coroot hG hP a Z t
  obtain ⟨n, hn, hnv⟩ := hindex v
  have hm : e ((n : ℤ) • v) ∈ cocharactersLandingIn i (locallyCommutatorFunctor G) :=
    hle hnv
  rw [map_smul] at hm
  exact cocharactersLandingIn_locallyCommutator_of_nsmul
    (D := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i (e v) n hn.ne' hm

/-- Every torus point is fppf-locally a commutator when the coroot lattice
has finite index in the full coordinate cocharacter lattice. -/
theorem locallyCommutator_torus_of_finiteIndex (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hindex : ∀ v : I → ℤ, ∃ n : ℕ, 0 < n ∧ (n : ℤ) • v ∈ P.corootSpan ℤ)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    LocallyCommutator (t ≫ i.hom.hom) := by
  classical
  let S := Spec (CommRingCat.of R)
  have ht : t = ∏ a : I,
      (t ≫ (CommGroupScheme.groupHom (splitTorus.proj S I a)).hom.hom) ≫
        (CommGroupScheme.groupHom (splitTorus.single S I a)).hom.hom := by
    have ht := comp_groupHom_sum t Finset.univ
      (fun a : I => splitTorus.proj S I a ≫ splitTorus.single S I a)
    rw [splitTorus.sum_proj_comp_single] at ht
    have hid : (CommGroupScheme.groupHom (𝟙 (splitTorus.commGroupScheme S I))).hom.hom =
        𝟙 (splitTorus (Spec (CommRingCat.of R)) I).X := rfl
    rw [hid, Category.comp_id] at ht
    exact ht.trans (Finset.prod_congr rfl fun a _ =>
      comp_groupHom_comp (G := splitTorus.commGroupScheme S I) t
        (splitTorus.proj S I a) (splitTorus.single S I a))
  let F := locallyCommutatorFunctor G
  let f : (Z ⟶ (splitTorus S I).X) →* (Z ⟶ G.X) :=
    ((yonedaGrp.map i).app (Opposite.op Z)).hom
  change t ∈ (F.carrier Z).comap f
  rw [ht]
  apply ((F.carrier Z).comap f).prod_mem
  intro a _
  have ha := exponentCocharacter_mem_locallyCommutator_of_finiteIndex hG hP hindex (Pi.single a 1)
  have he : splitTorus.exponentCocharacter S I (Pi.single a 1) = splitTorus.single S I a := by
    simp [splitTorus.exponentCocharacter, Pi.single_apply]
  rw [he] at ha
  exact ha Z (t ≫ (CommGroupScheme.groupHom (splitTorus.proj S I a)).hom.hom)

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.RelativeDerived

/-- On an empty test scheme, the empty fppf cover witnesses local membership. -/
theorem LocallyCommutator.of_isEmpty {S : Scheme.{u}} {G : GroupScheme S}
    {Z : Over S} [IsEmpty Z.left] (x : Z ⟶ G.X) : LocallyCommutator x := by
  refine ⟨Scheme.Cover.mkOfCovers PEmpty (fun a => a.elim) (fun a => a.elim)
    (fun z => isEmptyElim z) (fun a => a.elim), fun a => a.elim⟩

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

omit [DecidableEq I] in
/-- A semisimple field realization forces each coordinate vector to have a
positive multiple in the common integral coroot span. -/
theorem exists_pos_smul_mem_corootSpan_of_semisimpleField
    (hi : IsClosedSubgroup i) (hP : IsFibrewiseRootDatumOf I G i P)
    (k : Type u) [Field k] [Algebra R k]
    (hGk : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap R k)).obj G))
    (v : I → ℤ) : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • v ∈ P.corootSpan ℤ := by
  classical
  let Q := CoordinateRootDatum.fieldRealization k P
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hT : IsSplitTorus T.toGrp := isSplitTorus_splitTorus I
  have hi' : IsClosedSubgroup (splitTorus.baseChangeHom (K := k) G I i) :=
    (hi.baseChange (algebraBaseMap R k)).iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
    hGk.isConnectedReductive.isAffineHom
  have : Finite J := hP.finite
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have : Finite (cocharacterLattice T ⧸ Q.corootSpan ℤ) :=
    Q.finite_quotient_rootSpan_iff_corootSpan.mp
      (hGk.finite_quotient_rootSpan hT hi' (hP.field k))
  let e : cocharacterLattice T ≃ₗ[ℤ] (I → ℤ) :=
    (splitTorus.cocharacterLatticeEquiv k I).toIntLinearEquiv
  have hle : Q.corootSpan ℤ ≤ (P.corootSpan ℤ).comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change e (Q.coroot a) ∈ P.corootSpan ℤ
    rw [CoordinateRootDatum.fieldRealization_coroot,
      splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
    change (splitTorus.cocharacterLatticeEquiv k I)
      ((splitTorus.cocharacterLatticeEquiv k I).symm (P.coroot a)) ∈ _
    rw [AddEquiv.apply_symm_apply]
    exact Submodule.subset_span (Set.mem_range_self a)
  obtain ⟨n, hn, hnv⟩ :=
    (isOfFinAddOrder_of_finite ((Q.corootSpan ℤ).mkQ (e.symm v))).exists_nsmul_eq_zero
  have hm : (n : ℤ) • e.symm v ∈ Q.corootSpan ℤ := by
    apply (Submodule.Quotient.mk_eq_zero (Q.corootSpan ℤ)).mp
    change (Q.corootSpan ℤ).mkQ ((n : ℤ) • e.symm v) = 0
    rw [map_zsmul, natCast_zsmul]
    exact hnv
  have he := hle hm
  change e ((n : ℤ) • e.symm v) ∈ P.corootSpan ℤ at he
  rw [map_smul, LinearEquiv.apply_symm_apply] at he
  exact ⟨n, hn, he⟩

/-- Every point of the split torus in a relative semisimple reductive group
is fppf-locally in the abstract commutator subgroup. -/
theorem locallyCommutator_torus (hG : IsReductive G)
    (hss : ∀ s, IsSemisimple (geometricFiber G s)) (hi : IsClosedSubgroup i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    LocallyCommutator (t ≫ i.hom.hom) := by
  classical
  cases isEmpty_or_nonempty Z.left with
  | inl h => exact LocallyCommutator.of_isEmpty _
  | inr h =>
    let s := Z.hom (Classical.choice h)
    let k := (Spec (CommRingCat.of R)).residueField s
    let : Algebra R k :=
      (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
    apply locallyCommutator_torus_of_finiteIndex hG hP
    exact exists_pos_smul_mem_corootSpan_of_semisimpleField hi hP k
      (hG.isSemisimple_baseChange hss (algebraBaseMap R k))

end Langlands.GroupScheme.RelativeDerived
