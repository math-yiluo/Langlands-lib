import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

/-! # Distribution of actual sheaf tensor powers over a tensor product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Apply the actual sheaf tensor bifunctor to two isomorphisms. -/
def tensorMapIso {M M' N N' : X.Modules} (e : M ≅ M') (d : N ≅ N') :
    tensorObj M N ≅ tensorObj M' N' :=
  (tensorFunctor X).mapIso (e.prod d)

@[simp]
lemma tensorMapIso_hom {M M' N N' : X.Modules} (e : M ≅ M') (d : N ≅ N') :
    (tensorMapIso e d).hom = tensorMap e.hom d.hom :=
  rfl

@[simp]
lemma tensorMapIso_inv {M M' N N' : X.Modules} (e : M ≅ M') (d : N ≅ N') :
    (tensorMapIso e d).inv = tensorMap e.inv d.inv :=
  rfl

/-- Exchange the two middle factors of a fourfold actual sheaf tensor. -/
def tensorMiddleFourIso (A B C D : X.Modules) :
    tensorObj (tensorObj A B) (tensorObj C D) ≅
      tensorObj (tensorObj A C) (tensorObj B D) :=
  tensorAssociator A B (tensorObj C D) ≪≫
    tensorMapIso (Iso.refl A)
      ((tensorAssociator B C D).symm ≪≫
        tensorMapIso (tensorComm B C) (Iso.refl D) ≪≫ tensorAssociator C B D) ≪≫
    (tensorAssociator A C (tensorObj B D)).symm

/-- Distribute a nonnegative power of the actual sheaf tensor over its two factors. -/
def tensorPowTensorIso (M N : X.Modules) :
    (k : ℕ) → tensorPow (tensorObj M N) k ≅
      tensorObj (tensorPow M k) (tensorPow N k)
  | 0 => (tensorLeftUnitor (structureSheaf X)).symm
  | k + 1 =>
      tensorMapIso (Iso.refl (tensorObj M N)) (tensorPowTensorIso M N k) ≪≫
        tensorMiddleFourIso M N (tensorPow M k) (tensorPow N k)

/-- At zero the distribution isomorphism inserts the tensor square of the unit. -/
@[simp]
lemma tensorPowTensorIso_zero (M N : X.Modules) :
    tensorPowTensorIso M N 0 = (tensorLeftUnitor (structureSheaf X)).symm :=
  rfl

/-- At successor, distribute the tail and then exchange the two middle factors. -/
lemma tensorPowTensorIso_succ (M N : X.Modules) (k : ℕ) :
    tensorPowTensorIso M N (k + 1) =
      tensorMapIso (Iso.refl (tensorObj M N)) (tensorPowTensorIso M N k) ≪≫
        tensorMiddleFourIso M N (tensorPow M k) (tensorPow N k) :=
  rfl

@[simp]
lemma tensorPowTensorIso_zero_hom (M N : X.Modules) :
    (tensorPowTensorIso M N 0).hom = (tensorLeftUnitor (structureSheaf X)).inv :=
  rfl

@[simp]
lemma tensorPowTensorIso_zero_inv (M N : X.Modules) :
    (tensorPowTensorIso M N 0).inv = (tensorLeftUnitor (structureSheaf X)).hom :=
  rfl

set_option maxRecDepth 2048 in
/-- The forward successor map first distributes the tail and then regroups. -/
lemma tensorPowTensorIso_succ_hom (M N : X.Modules) (k : ℕ) :
    (tensorPowTensorIso M N (k + 1)).hom =
      tensorMap (𝟙 (tensorObj M N)) (tensorPowTensorIso M N k).hom ≫
        (tensorMiddleFourIso M N (tensorPow M k) (tensorPow N k)).hom :=
  by
    simp only [tensorPowTensorIso_succ, Iso.trans_hom, tensorMapIso_hom, Iso.refl_hom]
    rfl

set_option maxRecDepth 2048 in
/-- The inverse successor map first ungroups and then applies the inverse on the tail. -/
lemma tensorPowTensorIso_succ_inv (M N : X.Modules) (k : ℕ) :
    (tensorPowTensorIso M N (k + 1)).inv =
      (tensorMiddleFourIso M N (tensorPow M k) (tensorPow N k)).inv ≫
        tensorMap (𝟙 (tensorObj M N)) (tensorPowTensorIso M N k).inv :=
  by
    simp only [tensorPowTensorIso_succ, Iso.trans_inv, tensorMapIso_inv, Iso.refl_inv]
    rfl

end Langlands.Scheme.Modules
