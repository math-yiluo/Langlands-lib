import Langlands.Geometry.Analytic.TateUniversal.Definitions

/-! # Bounded algebra equivalences and their actual homeomorphisms -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

@[simp] theorem id_apply (a : A) : id K A a = a := rfl

@[simp] theorem comp_apply (g : BoundedAlgHom K B C) (f : BoundedAlgHom K A B)
    (a : A) : g.comp f a = g (f a) := rfl

@[simp] theorem id_comp (f : BoundedAlgHom K A B) : (id K B).comp f = f := rfl

@[simp] theorem comp_id (f : BoundedAlgHom K A B) : f.comp (id K A) = f := rfl

theorem comp_assoc {D : Type*} [NormedCommRing D] [Algebra K D]
    (h : BoundedAlgHom K C D) (g : BoundedAlgHom K B C)
    (f : BoundedAlgHom K A B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

end BoundedAlgHom

/-- An actual algebra equivalence with bounded forward and inverse maps.
Bounds are retained explicitly, including over trivially normed fields. -/
structure BoundedAlgEquiv (K : Type u) (A : Type v) (B : Type w)
    [NormedField K] [NormedCommRing A] [NormedCommRing B]
    [Algebra K A] [Algebra K B] extends A ≃ₐ[K] B where
  bounded : toAlgEquiv.toAlgHom.toRingHom.IsBounded
  inverse_bounded : toAlgEquiv.symm.toAlgHom.toRingHom.IsBounded

namespace BoundedAlgEquiv

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

instance : CoeFun (BoundedAlgEquiv K A B) (fun _ => A → B) :=
  ⟨fun e => e.toAlgEquiv⟩

/-- The forward bounded algebra map. -/
def toBoundedAlgHom (e : BoundedAlgEquiv K A B) : BoundedAlgHom K A B :=
  ⟨e.toAlgEquiv.toAlgHom, e.bounded⟩

/-- The inverse is bounded by the second bound of the equivalence. -/
def symm (e : BoundedAlgEquiv K A B) : BoundedAlgEquiv K B A where
  toAlgEquiv := e.toAlgEquiv.symm
  bounded := e.inverse_bounded
  inverse_bounded := e.bounded

@[simp] theorem symm_apply_apply (e : BoundedAlgEquiv K A B) (a : A) :
    e.symm (e a) = a := e.toAlgEquiv.symm_apply_apply a

@[simp] theorem apply_symm_apply (e : BoundedAlgEquiv K A B) (b : B) :
    e (e.symm b) = b := e.toAlgEquiv.apply_symm_apply b

@[simp] theorem toBoundedAlgHom_apply (e : BoundedAlgEquiv K A B) (a : A) :
    e.toBoundedAlgHom a = e a := rfl

/-- The identity has bound one in both directions. -/
def refl (K : Type u) (A : Type v) [NormedField K] [NormedCommRing A]
    [Algebra K A] : BoundedAlgEquiv K A A where
  toAlgEquiv := AlgEquiv.refl
  bounded := (BoundedAlgHom.id K A).bounded
  inverse_bounded := (BoundedAlgHom.id K A).bounded

/-- Compose the underlying algebra equivalences and their bounds. -/
def trans (e : BoundedAlgEquiv K A B) (d : BoundedAlgEquiv K B C) :
    BoundedAlgEquiv K A C where
  toAlgEquiv := e.toAlgEquiv.trans d.toAlgEquiv
  bounded := (d.toBoundedAlgHom.comp e.toBoundedAlgHom).bounded
  inverse_bounded := (e.symm.toBoundedAlgHom.comp d.symm.toBoundedAlgHom).bounded

/-- Package two explicitly constructed mutually inverse bounded maps. -/
def ofHomInv (f : BoundedAlgHom K A B) (g : BoundedAlgHom K B A)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) :
    BoundedAlgEquiv K A B where
  toAlgEquiv :=
    { f.toAlgHom with
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  bounded := f.bounded
  inverse_bounded := g.bounded

@[simp] theorem ofHomInv_apply (f : BoundedAlgHom K A B) (g : BoundedAlgHom K B A)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) (a : A) :
    ofHomInv f g hgf hfg a = f a := rfl

/-- A bounded algebra equivalence induces a homeomorphism of the actual
multiplicative spectra, contravariantly. -/
def spectrumHomeomorph (e : BoundedAlgEquiv K A B) :
    BanachSpectrum B ≃ₜ BanachSpectrum A where
  toFun := BanachSpectrum.comap e.toBoundedAlgHom.toBoundedRingHom
  invFun := BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
  left_inv x := by
    apply BanachSpectrum.ext
    intro b
    change x (e (e.symm b)) = x b
    rw [apply_symm_apply]
  right_inv x := by
    apply BanachSpectrum.ext
    intro a
    change x (e.symm (e a)) = x a
    rw [symm_apply_apply]
  continuous_toFun := (BanachSpectrum.comapContinuous
    e.toBoundedAlgHom.toBoundedRingHom).continuous
  continuous_invFun := (BanachSpectrum.comapContinuous
    e.symm.toBoundedAlgHom.toBoundedRingHom).continuous

@[simp] theorem spectrumHomeomorph_apply (e : BoundedAlgEquiv K A B)
    (x : BanachSpectrum B) (a : A) : e.spectrumHomeomorph x a = x (e a) := rfl

/-- The underlying norm topologies are equivalent as a consequence of the
two proved bounds; no open mapping theorem is required. -/
def toHomeomorph {R V W : Type*} [NormedField R]
    [NormedCommRing V] [NormedCommRing W]
    [NormedAlgebra R V] [NormedAlgebra R W]
    (e : BoundedAlgEquiv R V W) : V ≃ₜ W where
  toEquiv := e.toAlgEquiv.toEquiv
  continuous_toFun := e.toBoundedAlgHom.continuous
  continuous_invFun := e.symm.toBoundedAlgHom.continuous

end BoundedAlgEquiv

end Langlands.Analytic
