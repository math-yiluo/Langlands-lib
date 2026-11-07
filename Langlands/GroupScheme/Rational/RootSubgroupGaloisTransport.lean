import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.GaloisPointRational

/-! # Actual root subgroup transport under coefficient automorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

/-- Canonical descent for the actual commutative group, with its commutative structure. -/
def commDescentBaseChangeIso (T : CommGroupScheme B) :
    (CommGroupScheme.baseChange a).obj ((CommGroupScheme.baseChange b).obj T) ≅
      (CommGroupScheme.baseChange b).obj T where
  hom := Additive.ofMul (descentBaseChangeIso b a ha T.toGrp).hom
  inv := Additive.ofMul (descentBaseChangeIso b a ha T.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul (descentBaseChangeIso b a ha T.toGrp).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (descentBaseChangeIso b a ha T.toGrp).inv_hom_id

/-- Canonical descent carries the pulled-back character to its existing transport. -/
theorem characterLattice.congr_commDescentBaseChangeIso (T : CommGroupScheme B)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    characterLattice.congr (commDescentBaseChangeIso b a ha T)
      (characterLattice.baseChange a ((CommGroupScheme.baseChange b).obj T) χ) =
        characterLattice.transport b a ha T χ := rfl

namespace RelativeRoot

variable {T : CommGroupScheme B} {G : GroupScheme B} (i : T.toGrp ⟶ G)

/-- The canonical descent square transports the actual root subgroup on every test. -/
theorem subgroup_transportCharacter
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    subgroup (S := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) (characterLattice.transport b a ha T χ) =
      SubgroupFunctor.descentTransport b a ha G
        (subgroup (S := (CommGroupScheme.baseChange b).obj T)
          ((GroupScheme.baseChange b).map i) χ) := by
  have h :
      (subgroup (S := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) (characterLattice.transport b a ha T χ)).comap
          (descentBaseChangeIso b a ha G).hom =
      subgroup (S := (CommGroupScheme.baseChange a).obj
        ((CommGroupScheme.baseChange b).obj T))
        ((GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i))
        (characterLattice.baseChange a ((CommGroupScheme.baseChange b).obj T) χ) :=
    subgroup_comap_of_transport (commDescentBaseChangeIso b a ha T)
      (descentBaseChangeIso b a ha G) (descentBaseChangeIso_naturality b a ha i)
      (characterLattice.baseChange a ((CommGroupScheme.baseChange b).obj T) χ)
  have h' := h.trans (subgroup_baseChange a
    (S := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map i) χ)
  ext U x
  rw [SubgroupFunctor.mem_descentTransport]
  change x ∈ (subgroup (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)
      (characterLattice.transport b a ha T χ)).carrier U ↔
    x ≫ (descentBaseChangeIso b a ha G).inv.hom.hom ∈
      ((subgroup (S := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) χ).baseChange a).carrier U
  rw [← h', SubgroupFunctor.mem_comap]
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

end RelativeRoot

end Transport

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- Coefficient transport acts on the original all-test root subgroup by the actual
character-lattice action, without a splitness assumption. -/
theorem RelativeRoot.subgroup_galoisTransport (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    SubgroupFunctor.galoisTransport k K G σ
        (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) χ) =
      RelativeRoot.subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
        (characterLattice.galoisRepresentation k K T σ χ) :=
  (RelativeRoot.subgroup_transportCharacter (algebraBaseMap k K)
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) i χ).symm

end Galois

namespace GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The identity test with its structure twisted by `Spec σ` is isomorphic to
the identity test by that same spectrum automorphism. -/
def galoisIdentityTestIso (σ : K ≃ₐ[k] K) :
    (Over.map (galoisBaseMap k K σ)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≅
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
  Over.isoMk
    { hom := galoisBaseMap k K σ
      inv := galoisBaseMap k K σ⁻¹
      hom_inv_id := by
        rw [← galoisBaseMap_mul, mul_inv_cancel, galoisBaseMap_one]
        rfl
      inv_hom_id := by
        rw [← galoisBaseMap_mul, inv_mul_cancel, galoisBaseMap_one]
        rfl }
    (by simp)

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Coefficient conjugation, followed by canonical descent of a point, is
restriction of the original point along the coefficient spectrum map. -/
theorem descentPoint_rationalConjugate (σ : K ≃ₐ[k] K)
    (x : rationalPoints (baseChanged k K G)) :
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G (Over.mk (𝟙 _))
        (rationalConjugate k K G σ x) =
      (galoisIdentityTestIso k K σ).hom ≫ x := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) G
    ((Over.map (galoisBaseMap k K σ)).obj (Over.mk (𝟙 _)))).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_naturality]
  apply Over.OverMorphism.ext
  have h := congrArg (fun p => p.left)
    (baseChangeCoeffEquiv_rationalConjugate k K G σ x)
  rw [baseChangeCoeffEquiv_left] at h
  change (rationalConjugate k K G σ x).left ≫
      pullback.fst G.X.hom (baseMap k K) =
    galoisBaseMap k K σ ≫ (baseChangeCoeffEquiv k K G x).left at h
  rw [baseChangeCoeffEquiv_left] at h
  exact (Category.id_comp _).trans h

/-- Actual coefficient conjugation takes rational points of any all-test
subgroup precisely to rational points of its canonical transport. -/
theorem rationalConjugate_mem_galoisTransport_iff (σ : K ≃ₐ[k] K)
    (F : SubgroupFunctor (baseChanged k K G))
    (x : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ x ∈
        (SubgroupFunctor.galoisTransport k K G σ F).carrier (Over.mk (𝟙 _)) ↔
      x ∈ F.carrier (Over.mk (𝟙 _)) := by
  change rationalConjugate k K G σ x ∈
      (SubgroupFunctor.descentTransport (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G F).carrier (Over.mk (𝟙 _)) ↔ _
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint,
    descentPoint_rationalConjugate]
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using
      F.comp_mem (galoisIdentityTestIso k K σ).inv hx
  · exact F.comp_mem (galoisIdentityTestIso k K σ).hom

/-- Restriction of the actual coefficient automorphism to rational points of
an arbitrary all-test subgroup and its canonical transport. -/
def galoisTransportRationalEquiv (σ : K ≃ₐ[k] K)
    (F : SubgroupFunctor (baseChanged k K G)) :
    F.carrier (Over.mk (𝟙 _)) ≃*
      (SubgroupFunctor.galoisTransport k K G σ F).carrier (Over.mk (𝟙 _)) where
  toFun x := ⟨rationalConjugate k K G σ x,
    (rationalConjugate_mem_galoisTransport_iff k K G σ F x).mpr x.property⟩
  invFun x := ⟨(rationalConjugate k K G σ).symm x,
    (rationalConjugate_mem_galoisTransport_iff k K G σ F
      ((rationalConjugate k K G σ).symm x)).mp (by
        simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := by
    apply Subtype.ext
    change (rationalConjugate k K G σ).symm (rationalConjugate k K G σ x.val) = x.val
    exact (rationalConjugate k K G σ).left_inv x.val
  right_inv x := by
    apply Subtype.ext
    change rationalConjugate k K G σ ((rationalConjugate k K G σ).symm x.val) = x.val
    exact (rationalConjugate k K G σ).right_inv x.val
  map_mul' x y := by
    apply Subtype.ext
    change rationalConjugate k K G σ (x.val * y.val) =
      rationalConjugate k K G σ x.val * rationalConjugate k K G σ y.val
    exact (rationalConjugate k K G σ).map_mul x.val y.val

@[simp] theorem galoisTransportRationalEquiv_coe (σ : K ≃ₐ[k] K)
    (F : SubgroupFunctor (baseChanged k K G)) (x : F.carrier (Over.mk (𝟙 _))) :
    (galoisTransportRationalEquiv k K G σ F x).val =
      rationalConjugate k K G σ x := rfl

end GaloisPointComparison

namespace RelativeRoot

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

open GaloisPointComparison

/-- The existing coefficient conjugation transports the rational points of
each intrinsic root subgroup according to the actual character action. -/
theorem rationalConjugate_mem_subgroup_iff (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (x : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ x ∈
      (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
        (characterLattice.galoisRepresentation k K T σ χ)).carrier (Over.mk (𝟙 _)) ↔
      x ∈ (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) χ).carrier
          (Over.mk (𝟙 _)) := by
  rw [← subgroup_galoisTransport k K i σ χ]
  exact rationalConjugate_mem_galoisTransport_iff k K G σ _ x

/-- Multiplicative equivalence of the actual rational root subgroups,
with carrier map given by the existing coefficient conjugation. -/
def rationalGaloisEquiv (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) χ).carrier (Over.mk (𝟙 _)) ≃*
    (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (characterLattice.galoisRepresentation k K T σ χ)).carrier (Over.mk (𝟙 _)) :=
  (galoisTransportRationalEquiv k K G σ
      (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i) χ)).trans
    (MulEquiv.subgroupCongr (congrArg
      (fun F : SubgroupFunctor (baseChanged k K G) => F.carrier (Over.mk (𝟙 _)))
      (subgroup_galoisTransport k K i σ χ)))

@[simp] theorem rationalGaloisEquiv_coe (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (x : (subgroup (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) χ).carrier (Over.mk (𝟙 _))) :
    (rationalGaloisEquiv k K i σ χ x).val = rationalConjugate k K G σ x := by
  unfold rationalGaloisEquiv
  rfl

end RelativeRoot

end Langlands.GroupScheme
