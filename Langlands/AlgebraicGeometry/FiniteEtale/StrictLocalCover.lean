import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.RingTheory.TotallySplit

/-! # Geometric points of finite étale covers of a strictly local scheme -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

private theorem exists_section_at_point_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] (z : X) :
    ∃ q : Spec (.of k) ⟶ X, q ≫ p = 𝟙 _ ∧ q (IsLocalRing.closedPoint k) = z := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let f := Spec.preimage (X.isoSpec.inv ≫ p)
  have hf : Spec.map f = X.isoSpec.inv ≫ p := Spec.map_preimage _
  let A := Γ(X, ⊤)
  let : Algebra k A := f.hom.toAlgebra
  have : Algebra.Etale k A := by
    have h : Etale (Spec.map f) := by
      rw [hf]
      infer_instance
    exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)
  let e := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A
  let φ := e.symm (X.isoSpec.hom z)
  let q := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.isoSpec.inv
  refine ⟨q, ?_, ?_⟩
  · have hφ : f ≫ CommRingCat.ofHom φ.toRingHom = 𝟙 _ := by
      ext a
      exact φ.commutes a
    change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.isoSpec.inv) ≫ p = _
    rw [Category.assoc, ← hf, ← Spec.map_comp, hφ, Spec.map_id]
  · have hz : (Spec.map (CommRingCat.ofHom φ.toRingHom)) (IsLocalRing.closedPoint k) =
        X.isoSpec.hom z := by
      refine Eq.trans ?_ (e.apply_symm_apply (X.isoSpec.hom z))
      apply PrimeSpectrum.ext
      change Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal k) = RingHom.ker φ.toRingHom
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    change X.isoSpec.inv ((Spec.map (CommRingCat.ofHom φ.toRingHom))
      (IsLocalRing.closedPoint k)) = z
    rw [hz]
    exact congrArg (fun g : X ⟶ X => g z) X.isoSpec.hom_inv_id

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

local notation "S" => Spec (CommRingCat.of R)

private theorem exists_section_at_closed_point {X : Scheme.{u}} (p : X ⟶ S)
    [IsFinite p] [Etale p] (z : X) (hz : p z = IsLocalRing.closedPoint R) :
    ∃ σ : S ⟶ X, σ ≫ p = 𝟙 _ ∧ σ (IsLocalRing.closedPoint R) = z := by
  let k := IsLocalRing.ResidueField R
  let a := Spec.algebraMap R k
  have ha : a (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R k) (IsLocalRing.maximalIdeal k) = IsLocalRing.maximalIdeal R
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  obtain ⟨z', hz'₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := a) z
    (IsLocalRing.closedPoint k) (hz.trans ha.symm)
  obtain ⟨b, hb, hbz⟩ := exists_section_at_point_of_isSepClosed (pullback.snd p a) z'
  let c := b ≫ pullback.fst p a
  have hc : c ≫ p = a := by
    change (b ≫ pullback.fst p a) ≫ p = a
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  obtain ⟨σ, hσ, hσc⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      IsLocalRing.residue_surjective p c hc
  refine ⟨σ, hσ, ?_⟩
  have h := congrArg (fun q : Spec (.of k) ⟶ X => q (IsLocalRing.closedPoint k)) hσc
  change σ (a (IsLocalRing.closedPoint k)) = pullback.fst p a (b (IsLocalRing.closedPoint k)) at h
  rwa [ha, hbz, hz'₁] at h

private theorem exists_section_at_point {X : Scheme.{u}} (p : X ⟶ S)
    [IsFinite p] [Etale p] (z : X) :
    ∃ (σ : S ⟶ X), σ ≫ p = 𝟙 _ ∧ z ∈ Set.range σ := by
  let C := {σ : S ⟶ X // σ ≫ p = 𝟙 _}
  let U : Set X := ⋃ σ : C, Set.range σ.val
  have hU : IsOpen U := isOpen_iUnion fun σ => by
    have : IsOpenImmersion σ.val :=
      Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift.isOpenImmersion_of_section
        p σ.val σ.property
    exact σ.val.isOpenMap.isOpen_range
  have hzU : z ∈ U := by
    by_contra hz
    have hclosed : IsClosed (p '' Uᶜ) := p.isClosedMap _ hU.isClosed_compl
    have hmem : IsLocalRing.closedPoint R ∈ p '' Uᶜ :=
      (IsLocalRing.specializes_closedPoint (p z)).mem_closed hclosed ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hpy⟩ := hmem
    obtain ⟨σ, hσ, hyσ⟩ := exists_section_at_closed_point R p y hpy
    exact hy (Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, _, hyσ⟩)
  obtain ⟨σ, hzσ⟩ := Set.mem_iUnion.mp hzU
  exact ⟨σ.val, σ.property, hzσ⟩

/-- A geometric lift in a finite étale cover of a strictly Henselian local ring
is the evaluation of a section of the supplied cover. -/
def sectionOfGeometricLift {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (Y : Cover S) (x : Fiber s Y) :
    {σ : S ⟶ Y.obj.left // σ ≫ Y.obj.hom = 𝟙 _ ∧ s ≫ σ = x.left} := by
  classical
  let z := x.left (IsLocalRing.closedPoint Ω)
  let h := exists_section_at_point R Y.obj.hom z
  let σ := Classical.choose h
  have hσ : σ ≫ Y.obj.hom = 𝟙 _ := (Classical.choose_spec h).1
  have hz : z ∈ Set.range σ := (Classical.choose_spec h).2
  have : IsOpenImmersion σ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift.isOpenImmersion_of_section
      Y.obj.hom σ hσ
  have hsub : Set.range x.left ⊆ Set.range σ := by
    rintro _ ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := Spec (CommRingCat.of Ω)) t _
    rw [ht]
    exact hz
  let b := IsOpenImmersion.lift σ x.left hsub
  have hb : b ≫ σ = x.left := IsOpenImmersion.lift_fac _ _ _
  have hbs : b = s := by
    calc
      b = b ≫ (σ ≫ Y.obj.hom) := by rw [hσ, Category.comp_id]
      _ = s := by rw [← Category.assoc, hb]; exact Over.w x
  exact ⟨σ, hσ, (congrArg (fun u => u ≫ σ) hbs.symm).trans hb⟩

/-- The pointed finite étale fundamental group of a strictly Henselian local ring is trivial. -/
theorem subsingleton_fundamentalGroup_of_strictLocal {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y)) :
    Subsingleton (FundamentalGroup s hs) := by
  constructor
  intro g k
  apply fundamentalGroup_ext
  intro Y x
  let σ := sectionOfGeometricLift R s Y x
  let I : Cover S := cover (𝟙 S)
  let f : I ⟶ Y := ObjectProperty.homMk (Over.homMk σ.val σ.property.1)
  let t : Fiber s I := Over.homMk s (by simp [I, cover])
  have hx : t ≫ f.hom = x := Over.OverMorphism.ext σ.property.2
  have hfix (d : FundamentalGroup s hs) : d • t = t := by
    apply Over.OverMorphism.ext
    simpa [I, cover, t] using Over.w (d • t)
  rw [← hx, smul_naturality, smul_naturality, hfix, hfix]

end Langlands.AlgebraicGeometry.FiniteEtale
