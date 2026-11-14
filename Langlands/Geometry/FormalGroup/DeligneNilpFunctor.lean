import Langlands.Geometry.FormalGroup.DeligneAdmissibleBaseChange

/-! # The actual admissible Deligne class functor on Nilp algebras -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory _root_.AlgebraicGeometry

namespace Langlands.DeligneFormalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F]

namespace SheafDatum.IsoClass

variable (hπ : algebraMap O F π ≠ 0)
  {S S' S'' : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

/-- Actual pullback with a proved identification of the target global scalar map. -/
def pullbackTo (f : S' ⟶ S) {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ')
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    IsoClass (d := d) (π := π) (φ := φ') hπ :=
  hf ▸ pullback hπ f x

/-- Identity base change with any proof of the actual scalar identification. -/
theorem pullbackTo_id (hf : pulledGlobalScalar (𝟙 S) φ = φ)
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullbackTo hπ (𝟙 S) hf x = x := by
  change pullback hπ (𝟙 S) x = x
  exact pullback_id hπ x

/-- Scalar identifications respect composition of the actual pullbacks on classes. -/
theorem pullbackTo_comp (f : S' ⟶ S) (g : S'' ⟶ S')
    {φ' : O →+* Γ(S', ⊤)} {φ'' : O →+* Γ(S'', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (hg : pulledGlobalScalar g φ' = φ'')
    (hgf : pulledGlobalScalar (g ≫ f) φ = φ'')
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullbackTo hπ g hg (pullbackTo hπ f hf x) =
      pullbackTo hπ (g ≫ f) hgf x := by
  subst φ'
  subst φ''
  exact pullback_comp hπ f g x

/-- The scalar-aware class map depends only on the actual base morphism. -/
theorem pullbackTo_congr {f g : S' ⟶ S} (e : f = g)
    {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (hg : pulledGlobalScalar g φ = φ')
    (x : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullbackTo hπ f hf x = pullbackTo hπ g hg x := by
  subst g
  rfl

end SheafDatum.IsoClass

variable {B B' B'' : FormalGroup.Nilp.{u, u} O π}

/-- An algebra map in Nilp gives its actual contravariant morphism of affine schemes. -/
def nilpSpecMap (f : B ⟶ B') :
    Spec (CommRingCat.of B'.obj) ⟶ Spec (CommRingCat.of B.obj) :=
  Spec.map (CommRingCat.ofHom f.hom.hom.toRingHom)

@[simp]
theorem nilpSpecMap_id (B : FormalGroup.Nilp.{u, u} O π) :
    nilpSpecMap (𝟙 B) = 𝟙 (Spec (CommRingCat.of B.obj)) :=
  Spec.map_id _

@[simp]
theorem nilpSpecMap_comp (f : B ⟶ B') (g : B' ⟶ B'') :
    nilpSpecMap (f ≫ g) = nilpSpecMap g ≫ nilpSpecMap f := by
  change Spec.map ((forget₂ (CommAlgCat O) CommRingCat).map (f.hom ≫ g.hom)) = _
  rw [Functor.map_comp, Spec.map_comp]
  rfl

/-- The scalar map of Spec B' is the actual pullback of the scalar map of Spec B. -/
theorem nilpGlobalScalar_naturality (f : B ⟶ B') :
    pulledGlobalScalar (nilpSpecMap f) (nilpGlobalScalar π B) =
      nilpGlobalScalar π B' := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom f.hom.hom.toRingHom)
  apply RingHom.ext
  intro a
  have ha := congrArg (fun k => k.hom (algebraMap O B.obj a)) h
  change (Scheme.ΓSpecIso (CommRingCat.of B'.obj)).inv
      (f.hom.hom (algebraMap O B.obj a)) =
    (nilpSpecMap f).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of B.obj)).inv (algebraMap O B.obj a)) at ha
  rw [f.hom.hom.commutes] at ha
  exact ha.symm

variable (d π F) (hπ : algebraMap O F π ≠ 0)

/-- The actual map on admissible classes for an algebra morphism in Nilp. -/
def nilpSheafClassMap (f : B ⟶ B') :
    NilpSheafIsoClass d π F hπ B → NilpSheafIsoClass d π F hπ B' :=
  SheafDatum.IsoClass.pullbackTo hπ (nilpSpecMap f) (nilpGlobalScalar_naturality f)

@[simp]
theorem nilpSheafClassMap_id (B : FormalGroup.Nilp.{u, u} O π)
    (x : NilpSheafIsoClass d π F hπ B) :
    nilpSheafClassMap d π F hπ (𝟙 B) x = x := by
  unfold nilpSheafClassMap
  exact (SheafDatum.IsoClass.pullbackTo_congr hπ (nilpSpecMap_id B)
    (nilpGlobalScalar_naturality (𝟙 B)) rfl x).trans
      (SheafDatum.IsoClass.pullbackTo_id hπ rfl x)

theorem nilpSheafClassMap_comp (f : B ⟶ B') (g : B' ⟶ B'')
    (x : NilpSheafIsoClass d π F hπ B) :
    nilpSheafClassMap d π F hπ (f ≫ g) x =
      nilpSheafClassMap d π F hπ g (nilpSheafClassMap d π F hπ f x) := by
  unfold nilpSheafClassMap
  have hgf : pulledGlobalScalar (nilpSpecMap g ≫ nilpSpecMap f)
      (nilpGlobalScalar π B) = nilpGlobalScalar π B'' := by
    rw [← nilpSpecMap_comp]
    exact nilpGlobalScalar_naturality (f ≫ g)
  exact (SheafDatum.IsoClass.pullbackTo_congr hπ (nilpSpecMap_comp f g)
    (nilpGlobalScalar_naturality (f ≫ g)) hgf x).trans
      (SheafDatum.IsoClass.pullbackTo_comp hπ (nilpSpecMap f) (nilpSpecMap g)
        (nilpGlobalScalar_naturality f) (nilpGlobalScalar_naturality g) hgf x).symm

/-- Admissible four-data isomorphism classes form an actual covariant functor on Nilp. -/
def nilpSheafClassFunctor : FormalGroup.Nilp.{u, u} O π ⥤ Type (u + 1) where
  obj B := NilpSheafIsoClass d π F hπ B
  map f := ↾(nilpSheafClassMap d π F hπ f)
  map_id B := by
    ext x
    exact nilpSheafClassMap_id d π F hπ B x
  map_comp f g := by
    ext x
    exact nilpSheafClassMap_comp d π F hπ f g x

end Langlands.DeligneFormalSpace
