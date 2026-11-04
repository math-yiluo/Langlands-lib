import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # The actual kernel of a homomorphism of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace characterLattice

variable {S : Scheme.{u}} {T Q : CommGroupScheme S}

/-- Pullback of characters along an actual group-scheme homomorphism. -/
def comapHom (f : T.toGrp ⟶ Q.toGrp) : characterLattice Q →+ characterLattice T where
  toFun χ := Additive.ofMul f ≫ χ
  map_zero' := by simp
  map_add' χ ψ := by simp only [Preadditive.comp_add]

@[simp] theorem comapHom_groupHom (f : T.toGrp ⟶ Q.toGrp) (χ : characterLattice Q) :
    CommGroupScheme.groupHom (comapHom f χ) = f ≫ CommGroupScheme.groupHom χ := rfl

variable {k : Type u} [CommRing k] [IsDomain k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

omit [IsDomain k] in
/-- Character evaluation commutes with the actual homomorphism on every test scheme. -/
theorem pointCharacters_comp_hom (f : T.toGrp ⟶ Q.toGrp)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) (χ : characterLattice Q) :
    pointCharacters Q U (x ≫ f.hom.hom) (.ofAdd χ) =
      pointCharacters T U x (.ofAdd (comapHom f χ)) := by
  simp only [pointCharacters_apply, comapHom_groupHom, Grp.comp_hom_hom, Category.assoc]

end characterLattice

namespace Diagonalizable

section Quotient

variable {Λ : Type u} [AddCommGroup Λ] (N : AddSubgroup Λ)

/-- Characters which kill every element of the full subgroup of relations. -/
def subgroupAnnihilator (M : Type*) [CommGroup M] :
    Subgroup (Multiplicative Λ →* M) where
  carrier := {χ | ∀ b ∈ N, χ (.ofAdd b) = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro χ ψ hχ hψ b hb
    change χ (.ofAdd b) * ψ (.ofAdd b) = 1
    rw [hχ b hb, hψ b hb, one_mul]
  inv_mem' := by
    intro χ hχ b hb
    change (χ (.ofAdd b))⁻¹ = 1
    rw [hχ b hb, inv_one]

/-- The quotient by the full subgroup of relations, without saturation. -/
abbrev subgroupQuotient := Λ ⧸ N

/-- The actual quotient map on character groups. -/
abbrev subgroupQuotientMap : Λ →+ subgroupQuotient N := QuotientAddGroup.mk' N

/-- Restriction of quotient characters to the original character group. -/
def subgroupQuotientRestriction (M : Type*) [CommGroup M] :
    (Multiplicative (subgroupQuotient N) →* M) →* subgroupAnnihilator N M where
  toFun χ := ⟨χ.comp (AddMonoidHom.toMultiplicative (subgroupQuotientMap N)), by
    intro b hb
    change χ (.ofAdd (subgroupQuotientMap N b)) = 1
    rw [show subgroupQuotientMap N b = 0 from (QuotientAddGroup.eq_zero_iff b).mpr hb]
    exact map_one χ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem subgroupQuotientRestriction_apply (M : Type*) [CommGroup M]
    (χ : Multiplicative (subgroupQuotient N) →* M) (b : Λ) :
    (subgroupQuotientRestriction N M χ).val (.ofAdd b) =
      χ (.ofAdd (subgroupQuotientMap N b)) := rfl

theorem subgroupQuotientRestriction_injective (M : Type*) [CommGroup M] :
    Function.Injective (subgroupQuotientRestriction N M) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro q
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective N q.toAdd
  have h' := congrArg (fun f : subgroupAnnihilator N M => f.val (.ofAdd b)) h
  simpa only [subgroupQuotientRestriction_apply, hb, ofAdd_toAdd] using h'

theorem subgroupQuotientRestriction_surjective (M : Type*) [CommGroup M] :
    Function.Surjective (subgroupQuotientRestriction N M) := by
  intro χ
  let φ : Λ →+ Additive M :=
    { toFun := fun b => .ofMul (χ.val (.ofAdd b))
      map_zero' := congrArg Additive.ofMul χ.val.map_one
      map_add' := fun b c =>
        congrArg Additive.ofMul (χ.val.map_mul (.ofAdd b) (.ofAdd c)) }
  have hφ : N ≤ φ.ker := by
    intro b hb
    exact congrArg Additive.ofMul (χ.property b hb)
  refine ⟨AddMonoidHom.toMultiplicative (QuotientAddGroup.lift N φ hφ), ?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  rfl

/-- Characters of a quotient are exactly the characters killing its full relation subgroup. -/
def subgroupQuotientCharactersEquiv (M : Type*) [CommGroup M] :
    (Multiplicative (subgroupQuotient N) →* M) ≃* subgroupAnnihilator N M :=
  MulEquiv.ofBijective (subgroupQuotientRestriction N M)
    ⟨subgroupQuotientRestriction_injective N M,
      subgroupQuotientRestriction_surjective N M⟩

@[simp] theorem subgroupQuotientCharactersEquiv_apply (M : Type*) [CommGroup M]
    (χ : Multiplicative (subgroupQuotient N) →* M) (b : Λ) :
    (subgroupQuotientCharactersEquiv N M χ).val (.ofAdd b) =
      χ (.ofAdd (subgroupQuotientMap N b)) := rfl

@[simp] theorem subgroupQuotientCharactersEquiv_symm_apply (M : Type*) [CommGroup M]
    (χ : subgroupAnnihilator N M) (b : Λ) :
    (subgroupQuotientCharactersEquiv N M).symm χ (.ofAdd (subgroupQuotientMap N b)) =
      χ.val (.ofAdd b) :=
  congrArg (fun ψ : subgroupAnnihilator N M => ψ.val (.ofAdd b))
    ((subgroupQuotientCharactersEquiv N M).apply_symm_apply χ)

end Quotient

section Kernel

variable {k : Type u} [CommRing k] [IsDomain k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T.toGrp ⟶ Q.toGrp)

/-- The actual character group of the diagonalizable full kernel. -/
abbrev homKernelLattice := subgroupQuotient (characterLattice.comapHom f).range

/-- Points of the actual kernel are characters killing the image of pullback. -/
def homKernelCharacterPointsEquiv (hT : IsSplitTorus T.toGrp)
    (hQ : IsSplitTorus Q.toGrp) (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ (kernel f).X) ≃*
      subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ where
  toFun x := ⟨characterLattice.pointCharacters T U
    (x ≫ (kernelι f).hom.hom), by
      intro b hb
      obtain ⟨χ, rfl⟩ := hb
      rw [← characterLattice.pointCharacters_comp_hom]
      have hx : (x ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1 :=
        (kernelPointsEquiv f U x).property
      rw [hx, map_one]
      rfl⟩
  invFun χ := (kernelPointsEquiv f U).symm
    ⟨(characterLattice.pointCharactersEquiv T hT U).symm χ.val, by
      apply (characterLattice.pointCharactersEquiv Q hQ U).injective
      apply MonoidHom.ext
      intro b
      change characterLattice.pointCharacters Q U
          ((characterLattice.pointCharactersEquiv T hT U).symm χ.val ≫ f.hom.hom) b =
        characterLattice.pointCharacters Q U 1 b
      rw [map_one]
      change characterLattice.pointCharacters Q U
        ((characterLattice.pointCharactersEquiv T hT U).symm χ.val ≫ f.hom.hom)
          (.ofAdd b.toAdd) = 1
      rw [characterLattice.pointCharacters_comp_hom]
      change (characterLattice.pointCharactersEquiv T hT U
        ((characterLattice.pointCharactersEquiv T hT U).symm χ.val))
          (.ofAdd (characterLattice.comapHom f b.toAdd)) = 1
      rw [MulEquiv.apply_symm_apply]
      exact χ.property _ ⟨b.toAdd, rfl⟩⟩
  left_inv x := by
    apply (kernelPointsEquiv f U).injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply]
    change (characterLattice.pointCharactersEquiv T hT U).symm
      (characterLattice.pointCharactersEquiv T hT U
        (x ≫ (kernelι f).hom.hom)) = _
    exact (characterLattice.pointCharactersEquiv T hT U).symm_apply_apply _
  right_inv χ := by
    apply Subtype.ext
    change characterLattice.pointCharacters T U
      ((kernelPointsEquiv f U).symm _ ≫ (kernelι f).hom.hom) = χ.val
    rw [← kernelPointsEquiv_val, MulEquiv.apply_symm_apply]
    exact (characterLattice.pointCharactersEquiv T hT U).apply_symm_apply χ.val
  map_mul' x y := by
    apply Subtype.ext
    change characterLattice.pointCharacters T U
      ((x * y) ≫ (kernelι f).hom.hom) = _
    rw [MonObj.mul_comp, map_mul]
    rfl

/-- Restriction of annihilator characters under every change of test scheme. -/
def homAnnihilatorRestrict {U U' : Over (Spec (CommRingCat.of k))} (a : U' ⟶ U) :
    subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ →*
      subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U'.left, ⊤))ˣ where
  toFun χ := ⟨(Units.map a.left.appTop.hom.toMonoidHom).comp χ.val, by
    intro b hb
    change Units.map a.left.appTop.hom.toMonoidHom (χ.val (.ofAdd b)) = 1
    rw [χ.property b hb, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_one (Units.map a.left.appTop.hom.toMonoidHom)
  map_mul' χ ψ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_mul (Units.map a.left.appTop.hom.toMonoidHom) (χ.val b) (ψ.val b)

theorem homKernelCharacterPointsEquiv_naturality (hT : IsSplitTorus T.toGrp)
    (hQ : IsSplitTorus Q.toGrp) {U U' : Over (Spec (CommRingCat.of k))}
    (a : U' ⟶ U) (x : U ⟶ (kernel f).X) :
    homKernelCharacterPointsEquiv f hT hQ U' (a ≫ x) =
      homAnnihilatorRestrict f a (homKernelCharacterPointsEquiv f hT hQ U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change Gm.pointsEquiv _ U'
      (((a ≫ x) ≫ (kernelι f).hom.hom) ≫
        (CommGroupScheme.groupHom b.toAdd).hom.hom) =
    Units.map a.left.appTop.hom.toMonoidHom
      (Gm.pointsEquiv _ U
        ((x ≫ (kernelι f).hom.hom) ≫ (CommGroupScheme.groupHom b.toAdd).hom.hom))
  simp only [Category.assoc, Gm.pointsEquiv_naturality]

/-- The quotient diagonalizable group has the same annihilator model. -/
def homQuotientCharacterPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ (groupScheme (CommRingCat.of k) (homKernelLattice f)).X) ≃*
      subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ :=
  (characterPointsEquiv (CommRingCat.of k) (homKernelLattice f) U).trans
    (subgroupQuotientCharactersEquiv (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ)

omit [IsDomain k] in
theorem homQuotientCharacterPointsEquiv_naturality
    {U U' : Over (Spec (CommRingCat.of k))} (a : U' ⟶ U)
    (x : U ⟶ (groupScheme (CommRingCat.of k) (homKernelLattice f)).X) :
    homQuotientCharacterPointsEquiv f U' (a ≫ x) =
      homAnnihilatorRestrict f a (homQuotientCharacterPointsEquiv f U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv _ _ U' (a ≫ x)
    (.ofAdd (subgroupQuotientMap (characterLattice.comapHom f).range b.toAdd)) = _
  rw [characterPointsEquiv_naturality]
  rfl

/-- The full scheme-theoretic kernel is `D(coker(f*))`, retaining all torsion. -/
def homKernelDiagonalizableIso (hT : IsSplitTorus T.toGrp)
    (hQ : IsSplitTorus Q.toGrp) :
    kernel f ≅ (groupScheme (CommRingCat.of k) (homKernelLattice f)).toGrp :=
  isoOfPointModels
    (fun U : Over (Spec (CommRingCat.of k)) =>
      subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ)
    (fun a => homAnnihilatorRestrict f a)
    (homKernelCharacterPointsEquiv f hT hQ)
    (homQuotientCharacterPointsEquiv f)
    (homKernelCharacterPointsEquiv_naturality f hT hQ)
    (homQuotientCharacterPointsEquiv_naturality f)

/-- The inverse model evaluates a character on its full quotient class. -/
theorem homKernelDiagonalizableIso_inv (hT : IsSplitTorus T.toGrp)
    (hQ : IsSplitTorus Q.toGrp) (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ (groupScheme (CommRingCat.of k) (homKernelLattice f)).X)
    (b : characterLattice T) :
    Gm.pointsEquiv _ U
      (((x ≫ (homKernelDiagonalizableIso f hT hQ).inv.hom.hom) ≫
          (kernelι f).hom.hom) ≫ (CommGroupScheme.groupHom b).hom.hom) =
      characterPointsEquiv (CommRingCat.of k) (homKernelLattice f) U x
        (.ofAdd (subgroupQuotientMap (characterLattice.comapHom f).range b)) := by
  have h := isoOfPointModels_inv
    (fun U : Over (Spec (CommRingCat.of k)) =>
      subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ)
    (fun a => homAnnihilatorRestrict f a)
    (homKernelCharacterPointsEquiv f hT hQ)
    (homQuotientCharacterPointsEquiv f)
    (homKernelCharacterPointsEquiv_naturality f hT hQ)
    (homQuotientCharacterPointsEquiv_naturality f) U x
  exact congrArg (fun χ =>
    (χ : subgroupAnnihilator (characterLattice.comapHom f).range (Γ(U.left, ⊤))ˣ).val
      (.ofAdd b)) h

/-- The full kernel character group is finitely generated, with torsion retained. -/
theorem homKernelLattice_fg (hT : IsSplitTorus T.toGrp) :
    AddGroup.FG (homKernelLattice f) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let b := (splitTorus.characterLatticeEquiv k I).symm.trans c
  let : AddGroup.FG (characterLattice T) :=
    AddGroup.fg_of_surjective (f := b.toAddMonoidHom) b.surjective
  infer_instance

end Kernel

end Diagonalizable

end Langlands.GroupScheme
