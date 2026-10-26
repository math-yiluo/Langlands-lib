import Langlands.Geometry.Analytic.FiniteBanachAlgebra
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Automatic boundedness for maps out of finite Banach algebras -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NontriviallyNormedField K]
  [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [NormedAlgebra K A] [NormedAlgebra K B] [NormedAlgebra K C]
  [CompleteSpace A] [CompleteSpace B]

/-- A compatible algebraic map from a finite Banach algebra is bounded.
Finiteness refers to the exact map `f`, not an unrelated algebra structure. -/
def ofFiniteTriangle (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (h : B →ₐ[K] C) (comm : h.comp f.toAlgHom = g.toAlgHom) :
    BoundedAlgHom K B C where
  toAlgHom := h
  bounded := by
    let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
    let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower K A B := IsScalarTower.of_algHom f.toAlgHom
    let : IsScalarTower K A C := IsScalarTower.of_algHom g.toAlgHom
    let : Module.Finite A B := hf
    let hA : B →ₐ[A] C :=
      { h.toRingHom with
        commutes' := fun a => congrArg (fun q : A →ₐ[K] C => q a) comm }
    obtain ⟨M, hM, hbound⟩ := FiniteBanachAlgebra.exists_norm_bound
      (K := K) hA f.continuous g.continuous
    refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun b => ?_⟩
    exact (hbound b).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg b))

@[simp]
theorem ofFiniteTriangle_toAlgHom (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (h : B →ₐ[K] C) (comm : h.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteTriangle f hf g h comm).toAlgHom = h :=
  rfl

@[simp]
theorem ofFiniteTriangle_apply (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (h : B →ₐ[K] C) (comm : h.comp f.toAlgHom = g.toAlgHom) (b : B) :
    ofFiniteTriangle f hf g h comm b = h b :=
  rfl

/-- The constructed bounded map has the required base triangle. -/
theorem ofFiniteTriangle_comp (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (h : B →ₐ[K] C) (comm : h.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteTriangle f hf g h comm).comp f = g :=
  BoundedAlgHom.ext fun a => congrArg (fun q : A →ₐ[K] C => q a) comm

/-- Forgetting boundedness loses no maps in a triangle from a finite Banach
algebra. The target need not be complete. -/
def finiteTriangleEquiv (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C) :
    {h : B →ₐ[K] C // h.comp f.toAlgHom = g.toAlgHom} ≃
      {h : BoundedAlgHom K B C // h.comp f = g} where
  toFun h := ⟨ofFiniteTriangle f hf g h.1 h.2, ofFiniteTriangle_comp f hf g h.1 h.2⟩
  invFun h := ⟨h.1.toAlgHom, congrArg BoundedAlgHom.toAlgHom h.2⟩
  left_inv _ := rfl
  right_inv h := by
    apply Subtype.ext
    exact BoundedAlgHom.ext fun _ => rfl

end Langlands.Analytic.BoundedAlgHom

namespace Langlands.Analytic.BoundedAlgEquiv

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NontriviallyNormedField K]
  [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [NormedAlgebra K A] [NormedAlgebra K B] [NormedAlgebra K C]
  [CompleteSpace A] [CompleteSpace B] [CompleteSpace C]

/-- An algebraic equivalence compatible with a finite bounded base map has
bounded forward and inverse maps. Finiteness of the other base map is derived. -/
def ofFiniteTriangle (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (e : B ≃ₐ[K] C) (comm : e.toAlgHom.comp f.toAlgHom = g.toAlgHom) :
    BoundedAlgEquiv K B C := by
  have hg : g.toAlgHom.toRingHom.Finite := by
    rw [← comm]
    exact (RingHom.Finite.of_surjective e.toAlgHom.toRingHom e.surjective).comp hf
  have comm_symm : e.symm.toAlgHom.comp g.toAlgHom = f.toAlgHom := by
    apply AlgHom.ext
    intro a
    have ha := congrArg (fun q : A →ₐ[K] C => q a) comm
    change e.symm (g.toAlgHom a) = f.toAlgHom a
    rw [← ha]
    exact e.symm_apply_apply _
  exact ofHomInv
    (BoundedAlgHom.ofFiniteTriangle f hf g e.toAlgHom comm)
    (BoundedAlgHom.ofFiniteTriangle g hg f e.symm.toAlgHom comm_symm)
    e.symm_apply_apply e.apply_symm_apply

@[simp]
theorem ofFiniteTriangle_toAlgEquiv (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (e : B ≃ₐ[K] C) (comm : e.toAlgHom.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteTriangle f hf g e comm).toAlgEquiv = e := by
  ext
  rfl

/-- The actual spectrum homeomorphism is seminorm pullback by the original
algebraic equivalence. -/
@[simp]
theorem ofFiniteTriangle_spectrumHomeomorph_apply (f : BoundedAlgHom K A B)
    (hf : f.toAlgHom.toRingHom.Finite) (g : BoundedAlgHom K A C)
    (e : B ≃ₐ[K] C) (comm : e.toAlgHom.comp f.toAlgHom = g.toAlgHom)
    (x : BanachSpectrum C) (b : B) :
    (ofFiniteTriangle f hf g e comm).spectrumHomeomorph x b = x (e b) :=
  rfl

end Langlands.Analytic.BoundedAlgEquiv
