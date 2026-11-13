import Langlands.GroupScheme.Rational.RootFiberTransitivity
import Langlands.GroupScheme.Rational.RootOrbitUnitValue
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning

/-! # Prescribed character values along a simple relative root -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace RootPairing.Base

variable {J M N : Type*} [Finite J] [AddCommGroup M] [AddCommGroup N]
  {P : RootDatum J M N} (B : P.Base)
  (e : Module.Basis B.support ℤ M) (he : ∀ s, e s = P.root s)

include he in
/-- Positive roots have nonnegative coordinates in the integral simple-root basis. -/
theorem simpleRootValue_repr_nonneg {j : J} (hj : B.IsPos j) (s : B.support) :
    0 ≤ e.repr (P.root j) s := by
  classical
  apply hj.induction_on_add
  · intro t ht
    rw [← he ⟨t, ht⟩, e.repr_self]
    simp only [Finsupp.single_apply]
    split <;> omega
  · intro t z x hx ht hz
    rw [hx, map_add, Finsupp.add_apply]
    exact add_nonneg ht (by
      rw [← he ⟨z, hz⟩, e.repr_self]
      simp only [Finsupp.single_apply]
      split <;> omega)


/-- If the root lattice is the full lattice, the simple roots form an integral basis. -/
private def integralBasis (hspan : P.rootSpan ℤ = ⊤) : Module.Basis B.support ℤ M :=
  Module.Basis.mk B.linearIndepOn_root (by
    change ⊤ ≤ Submodule.span ℤ (Set.range (P.root ∘ ((↑) : B.support → J)))
    rw [Set.range_comp, Subtype.range_coe, B.span_root_support, hspan])

omit [Finite J] in
private theorem integralBasis_apply (hspan : P.rootSpan ℤ = ⊤) (s : B.support) :
    B.integralBasis hspan s = P.root s :=
  Module.Basis.mk_apply _ _ _

end RootPairing.Base

namespace Langlands.GroupScheme

section Setup

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f

local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- Restriction to the original split torus, transported back through split
character base change. -/
private def restrictCharacter (hS : IsSplitTorus S.toGrp) :
    characterLattice T_K →+ characterLattice S :=
  (characterLattice.baseChangeEquiv b S hS).symm.toAddMonoidHom.comp
    { toFun := fun χ => f_K ≫ χ
      map_zero' := by simp
      map_add' := by intros; simp }

omit [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.toGrp.X.hom]
  [LocallyOfFiniteType T.toGrp.X.hom] in
private theorem restrictCharacter_baseChange (hS : IsSplitTorus S.toGrp)
    (χ : characterLattice T_K) :
    characterLattice.baseChange b S (restrictCharacter k K f hS χ) = f_K ≫ χ :=
  (characterLattice.baseChangeEquiv b S hS).apply_symm_apply _

omit [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.toGrp.X.hom]
  [LocallyOfFiniteType T.toGrp.X.hom] in
private theorem restrictCharacter_pairing (hS : IsSplitTorus S.toGrp)
    (ν : cocharacterLattice S) (χ : characterLattice T_K) :
    latticePairing T_K χ (cocharacterLattice.baseChange b T (ν ≫ f)) =
      latticePairing S (restrictCharacter k K f hS χ) ν := by
  calc
    _ = latticePairing S_K (f_K ≫ χ) (cocharacterLattice.baseChange b S ν) := by
      simp only [latticePairing_apply, cocharacterLattice.baseChange_comp, Category.assoc]
    _ = _ := by
      rw [← restrictCharacter_baseChange k K f hS, latticePairing_baseChange]


omit [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.toGrp.X.hom]
  [LocallyOfFiniteType T.toGrp.X.hom] in
private theorem restrictCharacter_galois (hS : IsSplitTorus S.toGrp)
    (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    restrictCharacter k K f hS (characterLattice.galoisRepresentation k K T σ χ) =
      restrictCharacter k K f hS χ := by
  apply (characterLattice.baseChangeEquiv b S hS).injective
  change characterLattice.baseChange b S _ = characterLattice.baseChange b S _
  rw [restrictCharacter_baseChange, restrictCharacter_baseChange,
    ← characterLattice.galoisRepresentation_precompose,
    ← restrictCharacter_baseChange k K f hS χ,
    characterLattice.galoisRepresentation_baseChange]

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)

include hP hcent hT in
omit [FiniteDimensional k K] [IsGalois k K] [Finite J] in
private theorem restrictCharacter_root_mem (t : J) :
    restrictCharacter k K f hf.1.1 (P.root t) ∈
      relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
  have ht : P.root t ∈ roots (T := T_K) (G := G_K) j_K := by
    rw [← hP.2.1]
    exact Set.mem_range_self t
  have hne := root_restrict_ne_zero_of_torusCentralizer k K f j hf.1.1 hT hcent
    ⟨P.root t, ht⟩
  apply (mem_roots_iff_exists_splittingField_restriction (k := k) (K := K)
    hf.1.1 hT f j _).mpr
  refine ⟨?_, P.root t, ht, (restrictCharacter_baseChange k K f hf.1.1 _).symm⟩
  intro hz
  apply hne
  rw [← restrictCharacter_baseChange k K f hf.1.1, hz, map_zero]

include hP hf hcent hT in
omit [FiniteDimensional k K] [IsGalois k K] [Finite J] in
private theorem regular_root_pairing (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν) (t : J) :
    P.root' t (cocharacterLattice.baseChange b T (show cocharacterLattice T from ν ≫ f)) ≠ 0 := by
  change P.toLinearMap (P.root t) _ ≠ 0
  rw [hP.1, restrictCharacter_pairing k K f hf.1.1]
  exact hν _ (restrictCharacter_root_mem k K f j hP hf hcent hT t)

variable [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem simpleRootFiber_mem_base
    {a : characterLattice S}
    (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
    (t : J) (ht : restrictCharacter k K f hf.1.1 (P.root t) = a) :
    t ∈ (IsRootDatumOf.regularCocharacterBase k K (P := P)
      (cocharacterLattice.baseChange b T (ν ≫ f))
      (regular_root_pairing k K f j hP hf hcent hT ν hν)).support := by
  let B := IsRootDatumOf.regularCocharacterBase k K (P := P)
    (cocharacterLattice.baseChange b T (ν ≫ f))
    (regular_root_pairing k K f j hP hf hcent hT ν hν)
  have hpos (z : J) : B.IsPos z ↔
      0 < latticePairing S (restrictCharacter k K f hf.1.1 (P.root z)) ν := by
    rw [IsRootDatumOf.regularCocharacterBase_isPos k K j hP,
      restrictCharacter_pairing k K f hf.1.1]
  apply (B.mem_support_iff_positive_indecomposable P t).mpr
  refine ⟨(hpos t).mpr (by rw [ht]; exact ha.1.2), ?_⟩
  intro x y hx hy heq
  apply ha.2
  refine ⟨restrictCharacter k K f hf.1.1 (P.root x),
    ⟨restrictCharacter_root_mem k K f j hP hf hcent hT x, (hpos x).mp hx⟩,
    restrictCharacter k K f hf.1.1 (P.root y),
    ⟨restrictCharacter_root_mem k K f j hP hf hcent hT y, (hpos y).mp hy⟩, ?_⟩
  rw [← ht, heq, map_add]


include hP hf hT in
omit [P.IsReduced] in
private theorem multipleSimpleRootFiber_coordinate_zero
    (hjc : IsClosedSubgroup j)
    (B : P.Base)
    (hpos : ∀ z : J, B.IsPos z ↔
      0 < latticePairing S (restrictCharacter k K f hf.1.1 (P.root z)) ν)
    (hsimple : ∀ d ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν,
      ∀ z : J, restrictCharacter k K f hf.1.1 (P.root z) = d → z ∈ B.support)
    (e : Module.Basis B.support ℤ (characterLattice T_K))
    (he : ∀ s, e s = P.root s)
    {a d : characterLattice S}
    (hd : d ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
    (hda : d ≠ a) (m : ℕ) (hm : 0 < m)
    (t : J) (ht : restrictCharacter k K f hf.1.1 (P.root t) = m • d)
    (s : B.support) (hs : restrictCharacter k K f hf.1.1 (P.root s) = a) :
    e.repr (P.root t) s = 0 := by
  classical
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  obtain ⟨δ, hδ⟩ := rootRestrictionFiber_nonempty k K j f hf.1.1 hT ⟨d, hd.1.1⟩
  obtain ⟨z, hz⟩ : δ.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact δ.property
  have hzr : restrictCharacter k K f hf.1.1 (P.root z) = d := by
    apply (characterLattice.baseChangeEquiv b S hf.1.1).injective
    change characterLattice.baseChange b S _ = characterLattice.baseChange b S _
    rw [restrictCharacter_baseChange, hz]
    exact hδ
  let A := IsRootDatumOf.galoisRootIndexAction k K j hP
  have hAr (σ : K ≃ₐ[k] K) (x : J) :
      P.root (A σ x) = characterLattice.galoisRepresentation k K T σ (P.root x) :=
    IsRootDatumOf.galoisRootIndexEquiv_root k K j hP σ x
  have hrestrict (σ : K ≃ₐ[k] K) (x : J) :
      restrictCharacter k K f hf.1.1 (P.root (A σ x)) =
        restrictCharacter k K f hf.1.1 (P.root x) := by
    rw [hAr, restrictCharacter_galois]
  have hzbase (σ : K ≃ₐ[k] K) : A σ z ∈ B.support := by
    apply hsimple d hd
    rw [hrestrict, hzr]
  have hzcoord (σ : K ≃ₐ[k] K) : e.repr (P.root (A σ z)) s = 0 := by
    rw [← he ⟨A σ z, hzbase σ⟩, e.repr_self]
    apply Finsupp.single_eq_of_ne
    intro hzs
    have hidx : s.val = A σ z := congrArg Subtype.val hzs
    apply hda
    calc
      d = restrictCharacter k K f hf.1.1 (P.root (A σ z)) :=
        (hrestrict σ z).trans hzr |>.symm
      _ = restrictCharacter k K f hf.1.1 (P.root s) := by rw [hidx]
      _ = a := hs
  have htpos (σ : K ≃ₐ[k] K) : B.IsPos (A σ t) := by
    apply (hpos _).mpr
    rw [hrestrict, ht, map_nsmul]
    exact nsmul_pos hd.1.2 hm.ne'
  have hnonneg (σ : K ≃ₐ[k] K) : 0 ≤ e.repr (P.root (A σ t)) s :=
    B.simpleRootValue_repr_nonneg e he (htpos σ) s
  have hsum : CharacterAveraging.galoisOrbitSum k K T (P.root t) =
      m • CharacterAveraging.galoisOrbitSum k K T (P.root z) := by
    have hlargest := (hf.of_comp hjc).isLargestSplitSubtorus
    have hTt : IsTorus T.toGrp := ⟨K, inferInstance, inferInstance, hT⟩
    have hres : f_K ≫ P.root t = f_K ≫ (m • P.root z) := by
      rw [← restrictCharacter_baseChange k K f hf.1.1,
        ← restrictCharacter_baseChange k K f hf.1.1,
        map_nsmul, ht, hzr]
    have hsum := IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq k K f
      hlargest hTt hres
    simpa only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum,
      map_nsmul, Finset.smul_sum] using hsum
  have hsumcoord : (∑ σ : K ≃ₐ[k] K, e.repr (P.root (A σ t)) s) = 0 := by
    have hh := congrArg (fun χ => e.repr χ s) hsum
    simpa only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum,
      map_sum, map_nsmul, Finsupp.finsetSum_apply, Finsupp.nsmul_apply, ← hAr,
      hzcoord, Finset.sum_const_zero, smul_zero] using hh
  have hle := Finset.single_le_sum (fun σ (_ : σ ∈ Finset.univ) => hnonneg σ)
    (Finset.mem_univ (1 : K ≃ₐ[k] K))
  have hone : A (1 : K ≃ₐ[k] K) t = t := by
    rw [map_one]
    rfl
  rw [hsumcoord, hone] at hle
  exact le_antisymm hle (by simpa only [hone] using hnonneg (1 : K ≃ₐ[k] K))

end Setup

attribute [local instance] rootsGaloisAction

/-- Prescribe an equivariant character value along one simple relative-root fiber,
with trivial values on the other simple-root and double-root fibers. -/
theorem exists_simpleRootValueCharacter :
∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (S T : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G),
    IsMaximalTorus j → IsClosedSubgroup j →
    IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j) →
    (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j →
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp →
    ∀ (J : Type u) [Finite J]
      (P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
        (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))),
      IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P →
      P.IsReduced → P.rootSpan ℤ = ⊤ →
    ∀ (ν : cocharacterLattice S), IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν →
    ∀ a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν,
    ∀ β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
      β ∈ rootRestrictionFiber k K j f a →
    ∀ c : Kˣ, (c : K) ∈ rootOrbitField k K j β →
    ∃ φ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) →+
        Additive Kˣ,
      (∀ (σ : K ≃ₐ[k] K)
          (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)),
        (((φ (characterLattice.galoisRepresentation k K T σ χ)).toMul : Kˣ) : K) =
          σ (((φ χ).toMul : Kˣ) : K)) ∧
      φ β.val = Additive.ofMul c ∧
      ∀ b ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν, b ≠ a →
        ∀ γ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
            (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
            ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
          (γ ∈ rootRestrictionFiber k K j f b ∨ γ ∈ rootRestrictionFiber k K j f (2 • b)) →
          φ γ.val = 0 := by
  intro k K _ _ _ _ _ S T G _ _ _ _ f j hj hjc hf hcent hT J _ P hP hred hspan
    ν hν a ha β hβ c hc
  classical
  let : P.IsReduced := hred
  let νK : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) :=
    cocharacterLattice.baseChange (algebraBaseMap k K) T (ν ≫ f)
  have hreg : ∀ t : J, P.root' t νK ≠ 0 :=
    regular_root_pairing k K f j hP hf hcent hT ν hν
  let B := IsRootDatumOf.regularCocharacterBase k K (P := P) νK hreg
  let e := B.integralBasis hspan
  have he (s : B.support) : e s = P.root s := B.integralBasis_apply hspan s
  have hpos (z : J) : B.IsPos z ↔
      0 < latticePairing S (restrictCharacter k K f hf.1.1 (P.root z)) ν := by
    rw [IsRootDatumOf.regularCocharacterBase_isPos k K j hP,
      restrictCharacter_pairing k K f hf.1.1]
  have hsimple : ∀ d ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν,
      ∀ z : J, restrictCharacter k K f hf.1.1 (P.root z) = d → z ∈ B.support := by
    intro d hd z hz
    exact simpleRootFiber_mem_base k K f j hP hf hcent hT ν hν hd z hz
  have hroot (z : J) : P.root z ∈ roots
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) := by
    rw [← hP.2.1]
    exact Set.mem_range_self z
  let rootOf (z : J) : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) := ⟨P.root z, hroot z⟩
  obtain ⟨ψ, hψ, hψβ, hoff⟩ := exists_rootOrbitValue k K j β c hc
  let v : B.support → Additive Kˣ := fun s => Additive.ofMul (ψ (rootOf s))
  let L : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) →ₗ[ℤ]
      Additive Kˣ := e.constr ℤ v
  have hL (s : B.support) : L (P.root s) = v s := by
    rw [← he s]
    exact e.constr_basis ℤ v s
  let A := IsRootDatumOf.descendedRegularCocharacterSimpleAction k K j hP (ν ≫ f) hreg
  have hAr (σ : K ≃ₐ[k] K) (s : B.support) :
      P.root (A σ s) = characterLattice.galoisRepresentation k K T σ (P.root s) :=
    IsRootDatumOf.descendedRegularCocharacterSimpleAction_root k K j hP (ν ≫ f) hreg σ s
  have hAroot (σ : K ≃ₐ[k] K) (s : B.support) : rootOf (A σ s) = σ • rootOf s := by
    apply Subtype.ext
    exact hAr σ s
  have hLv (σ : K ≃ₐ[k] K) (s : B.support) :
      L (characterLattice.galoisRepresentation k K T σ (P.root s)) =
        (Units.map σ.toMonoidHom).toAdditive (L (P.root s)) := by
    rw [← hAr, hL, hL]
    change Additive.ofMul (ψ (rootOf (A σ s))) =
      Additive.ofMul (Units.map σ.toMonoidHom (ψ (rootOf s)))
    rw [hAroot, hψ]
  have hLequiv (σ : K ≃ₐ[k] K) :
      L.comp (characterLattice.galoisRepresentation k K T σ) =
        ((Units.map σ.toMonoidHom).toAdditive.toIntLinearMap).comp L := by
    apply e.ext
    intro s
    simpa only [LinearMap.comp_apply, he, AddMonoidHom.coe_toIntLinearMap] using hLv σ s
  refine ⟨L.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro σ χ
    have hh := LinearMap.congr_fun (hLequiv σ) χ
    exact congrArg (fun x : Additive Kˣ => ((x.toMul : Kˣ) : K)) hh
  · obtain ⟨z, hz⟩ : β.val ∈ Set.range P.root := by
      rw [hP.2.1]
      exact β.property
    have hzr : restrictCharacter k K f hf.1.1 (P.root z) = a := by
      apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hf.1.1).injective
      change characterLattice.baseChange (algebraBaseMap k K) S _ =
        characterLattice.baseChange (algebraBaseMap k K) S _
      rw [restrictCharacter_baseChange, hz]
      exact hβ
    have hzbase := hsimple a ha z hzr
    have hrootβ : rootOf z = β := Subtype.ext hz
    change L β.val = Additive.ofMul c
    rw [← hz, hL ⟨z, hzbase⟩]
    change Additive.ofMul (ψ (rootOf z)) = Additive.ofMul c
    rw [hrootβ, hψβ]
  · intro d hd hda γ hγ
    obtain ⟨t, ht⟩ : γ.val ∈ Set.range P.root := by
      rw [hP.2.1]
      exact γ.property
    have hcoord (s : B.support)
        (hs : restrictCharacter k K f hf.1.1 (P.root s) = a) : e.repr (P.root t) s = 0 := by
      rcases hγ with hγ | hγ
      · apply multipleSimpleRootFiber_coordinate_zero k K f j hP hf hT ν
          hjc B hpos hsimple e he hd hda 1 (by omega) t _ s hs
        apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hf.1.1).injective
        change characterLattice.baseChange (algebraBaseMap k K) S _ =
          characterLattice.baseChange (algebraBaseMap k K) S _
        rw [restrictCharacter_baseChange, ht, one_smul]
        exact hγ
      · apply multipleSimpleRootFiber_coordinate_zero k K f j hP hf hT ν
          hjc B hpos hsimple e he hd hda 2 (by omega) t _ s hs
        apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hf.1.1).injective
        change characterLattice.baseChange (algebraBaseMap k K) S _ =
          characterLattice.baseChange (algebraBaseMap k K) S _
        rw [restrictCharacter_baseChange, ht]
        exact hγ
    change L γ.val = 0
    rw [← ht, Module.Basis.constr_apply]
    apply Finset.sum_eq_zero
    intro s hs
    change e.repr (P.root t) s • v s = 0
    by_cases hsa : restrictCharacter k K f hf.1.1 (P.root s) = a
    · rw [hcoord s hsa, zero_smul]
    · have hnot : rootOf s ∉ MulAction.orbit (K ≃ₐ[k] K) β := by
        intro horbit
        have hres := rootOrbit_subset_restrictionFiber k K j f a hβ horbit
        apply hsa
        apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hf.1.1).injective
        change characterLattice.baseChange (algebraBaseMap k K) S _ =
          characterLattice.baseChange (algebraBaseMap k K) S _
        rw [restrictCharacter_baseChange]
        exact hres
      have hv : v s = 0 := by
        change Additive.ofMul (ψ (rootOf s)) = 0
        rw [hoff _ hnot]
        rfl
      rw [hv, smul_zero]

end Langlands.GroupScheme
