import Langlands.GroupScheme.IntegralModel.SemilinearPoints

/-! # Integral isomorphisms from stable section transport -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]

/-- The fixed-ring extension property consumed by the construction below.
It is an explicit premise, with no arithmetic assertion about the ring. -/
def HasSmoothHomExtension : Prop :=
  ∀ (J H : GroupScheme (Spec (CommRingCat.of L))) (f : J ⟶ H)
    (Q : IntegralModel R L J) (P : IntegralModel R L H),
    Q.IsSmooth →
    (∀ g ∈ Q.integralPoints, rationalPoints.map f g ∈ P.integralPoints) →
    Nonempty (Q.Hom P f)

section Abstract

variable {H J : GroupScheme (Spec (CommRingCat.of L))}
  (P : IntegralModel R L H) (Q : IntegralModel R L J) (e : J ≅ H)
  (t : P.integralSections → Q.integralSections)
  (s s' : rationalPoints H → rationalPoints H)

/-- Surjective section transport and point stability give the forward
integral-point inclusion for an arbitrary generic isomorphism. -/
theorem map_mem_integralPoints_of_section_transport
    (ht : Function.Surjective t)
    (htransport : ∀ x, rationalPoints.map e.hom (Q.integralPointMap (t x)) =
      s (P.integralPointMap x))
    (hstable : ∀ g ∈ P.integralPoints, s g ∈ P.integralPoints)
    {g : rationalPoints J} (hg : g ∈ Q.integralPoints) :
    rationalPoints.map e.hom g ∈ P.integralPoints := by
  obtain ⟨y, hy⟩ := hg
  obtain ⟨x, hx⟩ := ht y
  have h := htransport x
  rw [hx, hy] at h
  exact h.symm ▸ hstable (P.integralPointMap x) ⟨x, rfl⟩

/-- The fixed-ring homomorphism extension property promotes stable exact
section transport to a compatible integral-model isomorphism. -/
def isoOfSectionTransport
    (hext : HasSmoothHomExtension (R := R) (L := L))
    (hP : P.IsSmooth) (hQ : Q.IsSmooth)
    (ht : Function.Surjective t)
    (htransport : ∀ x, rationalPoints.map e.hom (Q.integralPointMap (t x)) =
      s (P.integralPointMap x))
    (hss : ∀ g, s (s' g) = g)
    (hstable : ∀ g ∈ P.integralPoints, s g ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints, s' g ∈ P.integralPoints) :
    Q.Iso P e :=
  Iso.ofHoms
    (Classical.choice (hext J H e.hom Q P hQ
      (fun _ hg => map_mem_integralPoints_of_section_transport P Q e t s ht
        htransport hstable hg)))
    (Classical.choice (hext H J e.inv P Q hP
      (fun _ hg => inv_map_mem_integralPoints_of_section_transport P Q e t s s'
        htransport hss hstable' hg)))

/-- Change only the specified generic-fibre identification along an actual
isomorphism of generic groups. -/
def retarget : IntegralModel R L H where
  group := Q.group
  affine := Q.affine
  flat := Q.flat
  finiteType := Q.finiteType
  genericIso := Q.genericIso ≪≫ e

/-- Retargeting changes generic evaluation by the specified generic map. -/
theorem retarget_integralPointMap (x : Q.integralSections) :
    (Q.retarget e).integralPointMap x = rationalPoints.map e.hom (Q.integralPointMap x) := by
  change baseChangeSectionHom (Spec.algebraMap R L) Q.group x ≫
      (Q.genericIso.hom ≫ e.hom).hom.hom =
    (baseChangeSectionHom (Spec.algebraMap R L) Q.group x ≫
      Q.genericIso.hom.hom.hom) ≫ e.hom.hom.hom
  exact (Category.assoc _ _ _).symm

/-- Retargeting maps exactly the original integral-point image along the
specified generic isomorphism. -/
theorem retarget_integralPoints :
    (Q.retarget e).integralPoints = Q.integralPoints.map (rationalPoints.map e.hom) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Q.integralPointMap x, ⟨x, rfl⟩, (retarget_integralPointMap Q e x).symm⟩
  · rintro ⟨g, ⟨x, hx⟩, rfl⟩
    exact ⟨x, (retarget_integralPointMap Q e x).trans (congrArg _ hx)⟩

/-- Forward inclusion and integral-section preimages identify the full
point image of a retargeted model. -/
theorem retarget_integralPoints_eq_of_preimages
    (hforward : ∀ g ∈ Q.integralPoints, rationalPoints.map e.hom g ∈ P.integralPoints)
    (hback : ∀ g ∈ P.integralPoints, ∃ y : Q.integralSections,
      rationalPoints.map e.hom (Q.integralPointMap y) = g) :
    (Q.retarget e).integralPoints = P.integralPoints := by
  rw [retarget_integralPoints]
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hforward y hy
  · intro hg
    obtain ⟨y, hy⟩ := hback g hg
    exact ⟨Q.integralPointMap y, ⟨y, rfl⟩, hy⟩

/-- Retargeting preserves smoothness of the actual integral group. -/
theorem isSmooth_retarget (hQ : Q.IsSmooth) : (Q.retarget e).IsSmooth := hQ

end Abstract

/-- Two smooth models of the same group with equal integral-point images
are compatibly isomorphic, provided the fixed-ring extension criterion. -/
def isoOfIntegralPointsEq {H : GroupScheme (Spec (CommRingCat.of L))}
    (P Q : IntegralModel R L H)
    (hext : HasSmoothHomExtension (R := R) (L := L))
    (hP : P.IsSmooth) (hQ : Q.IsSmooth)
    (hpoints : P.integralPoints = Q.integralPoints) :
    P.Iso Q (CategoryTheory.Iso.refl H) := by
  have hid (g : rationalPoints H) : rationalPoints.map (𝟙 H) g = g := by
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
  exact Iso.ofHoms
    (Classical.choice (hext H H (𝟙 H) P Q hP (fun g hg => by
      rw [hid, ← hpoints]
      exact hg)))
    (Classical.choice (hext H H (𝟙 H) Q P hQ (fun g hg => by
      rw [hid, hpoints]
      exact hg)))


section Galois

open GaloisPointComparison

variable (k : Type u) [Field k] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (P : IntegralModel R L (baseChanged k L G))
  (σ : L ≃ₐ[k] L)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (hσ : galoisBaseMap k L σ ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)

theorem galoisDescentIso_map_eq :
    rationalPoints.map (galoisDescentIso k L G σ).hom =
      rationalPoints.map
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom :=
  congrArg (fun e => rationalPoints.map e.hom) (galoisDescentIso_def k L G σ)

theorem galoisDescentIso_hom_eq :
    (galoisDescentIso k L G σ).hom =
      (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom :=
  congrArg (fun e => e.hom) (galoisDescentIso_def k L G σ)

theorem twist_integralPointMap_galoisIso (x : P.integralSections) :
    rationalPoints.map (galoisDescentIso k L G σ).hom
        ((P.twist a (galoisBaseMap k L σ) hσ).integralPointMap
          (baseChangeSectionHom a P.group x)) =
      rationalConjugate k L G σ (P.integralPointMap x) :=
  (DFunLike.congr_fun (galoisDescentIso_map_eq k G σ) _).trans
    (twist_integralPointMap_galois k G P σ a hσ x)

/-- Inverse stability supplies the reverse point-inclusion premise for the
same canonical isomorphism, with its base-change objects named explicitly. -/
theorem galoisTwist_inv_map_mem_integralPoints
    (hstable : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm g ∈ P.integralPoints)
    {g : rationalPoints (baseChanged k L G)} (hg : g ∈ P.integralPoints) :
    rationalPoints.map (galoisDescentIso k L G σ).inv g ∈
      (P.twist a (galoisBaseMap k L σ) hσ).integralPoints :=
  inv_map_mem_integralPoints_of_section_transport P
    (P.twist a (galoisBaseMap k L σ) hσ) (galoisDescentIso k L G σ)
    (baseChangeSectionHom a P.group)
    (rationalConjugate k L G σ) (rationalConjugate k L G σ.symm)
    (twist_integralPointMap_galoisIso k G P σ a hσ)
    (rationalConjugate_symm_apply k L G σ) hstable hg

/-- Actual integral Galois semilinear isomorphism, conditional on the
fixed-ring extension property and stability under σ and its inverse. -/
def galoisTwistIso [IsIso a]
    (hext : HasSmoothHomExtension (R := R) (L := L))
    (hP : P.IsSmooth)
    (hstable : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ g ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm g ∈ P.integralPoints) :
    (P.twist a (galoisBaseMap k L σ) hσ).Iso P (galoisDescentIso k L G σ) :=
  isoOfSectionTransport P (P.twist a (galoisBaseMap k L σ) hσ)
    (galoisDescentIso k L G σ)
    (baseChangeSectionHom a P.group)
    (rationalConjugate k L G σ) (rationalConjugate k L G σ.symm)
    hext hP (P.isSmooth_twist a (galoisBaseMap k L σ) hσ hP)
    (baseChangeSectionHom_surjective a P.group)
    (twist_integralPointMap_galoisIso k G P σ a hσ)
    (rationalConjugate_symm_apply k L G σ) hstable hstable'

/-- The conditional integral isomorphism has the exact canonical generic
semilinear law used by the descent solution comparison. -/
theorem galoisTwistIso_generic_comm [IsIso a]
    (hext : HasSmoothHomExtension (R := R) (L := L))
    (hP : P.IsSmooth)
    (hstable : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ g ∈ P.integralPoints)
    (hstable' : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ.symm g ∈ P.integralPoints) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map P.genericIso.hom ≫
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom =
      (Descent.squareComparison (Spec.algebraMap R L) (galoisBaseMap k L σ) a
        (Spec.algebraMap R L) hσ P.group).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R L)).map
          (galoisTwistIso k G P σ a hσ hext hP hstable hstable').iso.hom ≫
            P.genericIso.hom := by
  have h := Hom.twist_generic_comm P a (galoisBaseMap k L σ) hσ
    (galoisTwistIso k G P σ a hσ hext hP hstable hstable').toHom
  exact (congrArg
    (fun f => (GroupScheme.baseChange (galoisBaseMap k L σ)).map P.genericIso.hom ≫ f)
    (galoisDescentIso_hom_eq k G σ)).symm.trans h

end Galois
end Langlands.GroupScheme.IntegralModel
