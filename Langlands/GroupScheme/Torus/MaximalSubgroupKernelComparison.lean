import Langlands.GroupScheme.CommutativeSubgroupIntersection
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.KernelCocharacters
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Compatible maximal subgroup tori and full restricted kernels -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {M D : GroupScheme (Spec (CommRingCat.of k))}
    {S T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A maximal torus of a closed subgroup, compatibly contained in an ambient
torus, is the full intersection whenever that intersection is a torus. -/
def maximalSubgroupTorusIntersectionIso
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d)) :
    S.toGrp ≅ subgroupIntersection t d := by
  letI : IsClosedImmersion d.hom.hom.left := hd
  letI : Mono d.hom.hom := Over.mono_of_mono_left _
  let l := commutativeSubgroupIntersectionLift t d (CommGroupScheme.groupHom φ) s h
  let hl : IsIso l :=
    hs.2.2 (commutativeSubgroupIntersection t d)
      (commutativeSubgroupIntersectionSnd t d) l hI
      (isClosedSubgroup_commutativeSubgroupIntersectionSnd t d ht)
      (commutativeSubgroupIntersectionLift_snd t d _ _ h)
  exact @asIso _ _ _ _ l hl

@[reassoc]
theorem maximalSubgroupTorusIntersectionIso_hom_fst
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d)) :
    (maximalSubgroupTorusIntersectionIso t d s φ ht hd hs h hI).hom ≫
      subgroupIntersectionFst t d = CommGroupScheme.groupHom φ := by
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  unfold maximalSubgroupTorusIntersectionIso
  exact commutativeSubgroupIntersectionLift_fst t d _ _ h

@[reassoc]
theorem maximalSubgroupTorusIntersectionIso_hom_snd
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d)) :
    (maximalSubgroupTorusIntersectionIso t d s φ ht hd hs h hI).hom ≫
      subgroupIntersectionSnd t d = s := by
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  unfold maximalSubgroupTorusIntersectionIso
  exact commutativeSubgroupIntersectionLift_snd t d _ _ h

/-- If the closed subgroup is the full kernel of a supplied map, the
compatible maximal torus is the full actual kernel of its restriction. -/
def maximalSubgroupTorusKernelIso
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (q : M ⟶ Q.toGrp)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d))
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d) :
    S ≅ CommGroupScheme.kernel (Additive.ofMul (t ≫ q) : T ⟶ Q) :=
  CommGroupScheme.isoOfGroupIso
    (maximalSubgroupTorusIntersectionIso t d s φ ht hd hs h hI ≪≫
      (kernelCompositeIntersectionIso t d q hd hker).symm)

@[reassoc]
theorem maximalSubgroupTorusKernelIso_hom_comp
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (q : M ⟶ Q.toGrp)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d))
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d) :
    (maximalSubgroupTorusKernelIso t d s φ q ht hd hs h hI hker).hom ≫
      CommGroupScheme.kernelι (Additive.ofMul (t ≫ q) : T ⟶ Q) = φ := by
  apply Additive.toMul.injective
  change
    ((maximalSubgroupTorusIntersectionIso t d s φ ht hd hs h hI).hom ≫
      (kernelCompositeIntersectionIso t d q hd hker).inv) ≫ kernelι (t ≫ q) =
        CommGroupScheme.groupHom φ
  rw [Category.assoc, ← kernelCompositeIntersectionIso_hom_comp t d q hd hker,
    Iso.inv_hom_id_assoc, maximalSubgroupTorusIntersectionIso_hom_fst]

/-- The compatible subgroup torus has precisely the cocharacters killed by
the restricted map, with the actual integral maps retained. -/
def maximalSubgroupTorusCocharacterKernelEquiv
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (q : M ⟶ Q.toGrp)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d))
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d) :
    cocharacterLattice S ≃+
      (CommGroupScheme.postcompose (Additive.ofMul (t ≫ q) : T ⟶ Q)
        (Gm (Spec (CommRingCat.of k)))).ker :=
  (cocharacterLattice.congr
      (maximalSubgroupTorusKernelIso t d s φ q ht hd hs h hI hker)).trans
    (cocharacterLattice.kernelEquiv (Additive.ofMul (t ≫ q) : T ⟶ Q))

@[simp]
theorem maximalSubgroupTorusCocharacterKernelEquiv_val
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (q : M ⟶ Q.toGrp)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d))
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d)
    (ν : cocharacterLattice S) :
    (maximalSubgroupTorusCocharacterKernelEquiv t d s φ q ht hd hs h hI hker ν).val =
      ν ≫ φ := by
  change (ν ≫ (maximalSubgroupTorusKernelIso t d s φ q ht hd hs h hI hker).hom) ≫
    CommGroupScheme.kernelι (Additive.ofMul (t ≫ q) : T ⟶ Q) = ν ≫ φ
  rw [Category.assoc, maximalSubgroupTorusKernelIso_hom_comp]

/-- Exactness on actual integral cocharacters follows from the full kernel
comparison, without requiring a splitting field or a coroot basis. -/
theorem cocharacter_comp_eq_zero_iff_of_maximalSubgroupTorus
    (t : T.toGrp ⟶ M) (d : D ⟶ M) (s : S.toGrp ⟶ D) (φ : S ⟶ T)
    (q : M ⟶ Q.toGrp)
    (ht : IsClosedSubgroup t) (hd : IsClosedSubgroup d) (hs : IsMaximalTorus s)
    (h : CommGroupScheme.groupHom φ ≫ t = s ≫ d)
    (hI : IsTorus (subgroupIntersection t d))
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d)
    (ν : cocharacterLattice T) :
    ν ≫ (Additive.ofMul (t ≫ q) : T ⟶ Q) = 0 ↔
      ∃ η : cocharacterLattice S, η ≫ φ = ν := by
  let e := maximalSubgroupTorusCocharacterKernelEquiv t d s φ q ht hd hs h hI hker
  constructor
  · intro hν
    obtain ⟨η, hη⟩ := e.surjective ⟨ν, hν⟩
    refine ⟨η, ?_⟩
    have he := congrArg Subtype.val hη
    exact (maximalSubgroupTorusCocharacterKernelEquiv_val
      t d s φ q ht hd hs h hI hker η).symm.trans he
  · rintro ⟨η, rfl⟩
    have he := (e η).property
    change (e η).val ≫ (Additive.ofMul (t ≫ q) : T ⟶ Q) = 0 at he
    rwa [show (e η).val = η ≫ φ from
      maximalSubgroupTorusCocharacterKernelEquiv_val
        t d s φ q ht hd hs h hI hker η] at he

end Langlands.GroupScheme
