import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Maps of finite-length smooth Grothendieck groups induced by functors

A functor between actual smooth representation categories that preserves
group-algebra finite length and actual short exact sequences of finite-length
objects induces an integer-linear map between the exact Grothendieck groups of
finite-length representations. The coefficient rings, groups and carrier
universes of source and target are independent.
-/

noncomputable section

open CategoryTheory

universe uR uG uV uS uH uW uT uK uX uF

namespace Langlands.SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  {S : Type uS} {H : Type uH} [CommRing S] [Group H] [TopologicalSpace H]
  {T : Type uT} {K : Type uK} [CommRing T] [Group K] [TopologicalSpace K]

/-- The functor sends every actual smooth representation of finite group-algebra
length to one of finite group-algebra length. -/
def PreservesFiniteLength
    (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H) : Prop :=
  ∀ A : SmoothRep.{uR, uG, uV} R G, A.HasFiniteLength → (Φ.obj A).HasFiniteLength

/-- The functor sends every actual short exact sequence of finite-length smooth
representations, read through the underlying intertwiners, to an actual short
exact sequence. -/
def PreservesFiniteLengthShortExact
    (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H) : Prop :=
  ∀ ⦃A B C : SmoothRep.{uR, uG, uV} R G⦄ (f : A ⟶ B) (g : B ⟶ C),
    A.HasFiniteLength → B.HasFiniteLength → C.HasFiniteLength →
      IsShortExact (hom f) (hom g) → IsShortExact (hom (Φ.map f)) (hom (Φ.map g))

theorem preservesFiniteLength_id :
    PreservesFiniteLength (𝟭 (SmoothRep.{uR, uG, uV} R G)) :=
  fun _ hA => hA

theorem preservesFiniteLengthShortExact_id :
    PreservesFiniteLengthShortExact (𝟭 (SmoothRep.{uR, uG, uV} R G)) :=
  fun _ _ _ _ _ _ _ _ h => h

theorem PreservesFiniteLength.comp
    {Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    {Ψ : SmoothRep.{uS, uH, uW} S H ⥤ SmoothRep.{uT, uK, uX} T K}
    (hΦ : PreservesFiniteLength Φ) (hΨ : PreservesFiniteLength Ψ) :
    PreservesFiniteLength (Φ ⋙ Ψ) :=
  fun A hA => hΨ (Φ.obj A) (hΦ A hA)

/-- Finite-length preservation by the first functor is needed because the
second functor's exactness is only assumed for finite-length terms. -/
theorem PreservesFiniteLengthShortExact.comp
    {Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    {Ψ : SmoothRep.{uS, uH, uW} S H ⥤ SmoothRep.{uT, uK, uX} T K}
    (hΦl : PreservesFiniteLength Φ) (hΦ : PreservesFiniteLengthShortExact Φ)
    (hΨ : PreservesFiniteLengthShortExact Ψ) :
    PreservesFiniteLengthShortExact (Φ ⋙ Ψ) :=
  fun A B C f g hA hB hC h =>
    hΨ (Φ.map f) (Φ.map g) (hΦl A hA) (hΦl B hB) (hΦl C hC) (hΦ f g hA hB hC h)

namespace FiniteLengthGrothendieckGroup

/-- The actual image of a finite-length object, with its finite-length proof. -/
def mapObject (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) (A : FiniteLengthObject.{uR, uG, uV} R G) :
    FiniteLengthObject.{uS, uH, uW} S H :=
  ⟨Φ.obj A.val, hl A.val A.property⟩

/-- The class function sending the class of `A` to the class of `Φ.obj A`.
It is well defined because a functor maps isomorphisms to isomorphisms. -/
def mapClass (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) :
    FiniteLengthIsoClass.{uR, uG, uV} R G → FiniteLengthGrothendieckGroup.{uS, uH, uW} S H :=
  Quotient.lift (s := finiteLengthIsoSetoid R G) (fun A => ofObject (mapObject Φ hl A))
    (fun _ _ h => h.elim fun e => ofObject_eq_of_iso (Φ.mapIso e))

@[simp] theorem mapClass_finiteLengthIsoClass
    (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) (A : FiniteLengthObject.{uR, uG, uV} R G) :
    mapClass Φ hl (finiteLengthIsoClass A) = ofObject (mapObject Φ hl A) :=
  rfl

/-- Preservation of actual short exact sequences makes the class function
exact additive. Each defining intertwiner enters as the morphism `ofHom f`. -/
theorem isExactAdditive_mapClass
    (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    IsExactAdditive R G (mapClass Φ hl) := by
  intro A B C f g h
  exact ofObject_shortExact (A := mapObject Φ hl A) (B := mapObject Φ hl B)
    (C := mapObject Φ hl C)
    (hx (ofHom f) (ofHom g) A.property B.property C.property h)

/-- The integer-linear map of exact Grothendieck groups induced by a functor
preserving finite length and short exact sequences of finite-length objects. -/
def map (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uS, uH, uW} S H :=
  lift R G (mapClass Φ hl) (isExactAdditive_mapClass Φ hl hx)

section Generators

variable (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
  (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ)

@[simp] theorem map_ofClass (c : FiniteLengthIsoClass.{uR, uG, uV} R G) :
    map Φ hl hx (ofClass R G c) = mapClass Φ hl c :=
  lift_ofClass R G _ _ c

@[simp] theorem map_ofObject (A : FiniteLengthObject.{uR, uG, uV} R G) :
    map Φ hl hx (ofObject A) = ofObject (mapObject Φ hl A) :=
  lift_ofObject R G _ _ A

/-- The generator computation on an actual finite-length representation. -/
@[simp] theorem map_ofRepresentation (A : SmoothRep.{uR, uG, uV} R G)
    (hA : A.HasFiniteLength) :
    map Φ hl hx (ofRepresentation A hA) = ofRepresentation (Φ.obj A) (hl A hA) :=
  lift_ofRepresentation R G _ _ A hA

end Generators

/-- The identity functor induces the identity, for any proofs of its
preservation properties. -/
theorem map_id (hl : PreservesFiniteLength (𝟭 (SmoothRep.{uR, uG, uV} R G)))
    (hx : PreservesFiniteLengthShortExact (𝟭 (SmoothRep.{uR, uG, uV} R G))) :
    map (𝟭 (SmoothRep.{uR, uG, uV} R G)) hl hx = LinearMap.id := by
  apply hom_ext_object R G
  intro A
  rw [map_ofObject, LinearMap.id_apply]
  rfl

/-- A composite functor induces the composite map, for any proofs of the
composite's preservation properties. -/
theorem map_comp (Φ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H)
    (Ψ : SmoothRep.{uS, uH, uW} S H ⥤ SmoothRep.{uT, uK, uX} T K)
    (hΦl : PreservesFiniteLength Φ) (hΦx : PreservesFiniteLengthShortExact Φ)
    (hΨl : PreservesFiniteLength Ψ) (hΨx : PreservesFiniteLengthShortExact Ψ)
    (hl : PreservesFiniteLength (Φ ⋙ Ψ)) (hx : PreservesFiniteLengthShortExact (Φ ⋙ Ψ)) :
    map (Φ ⋙ Ψ) hl hx = (map Ψ hΨl hΨx).comp (map Φ hΦl hΦx) := by
  apply hom_ext_object R G
  intro A
  rw [LinearMap.comp_apply, map_ofObject, map_ofObject, map_ofObject]
  rfl

/-- Naturally isomorphic functors induce the same map. -/
theorem map_eq_of_iso {Φ Ψ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    (e : Φ ≅ Ψ) (hΦl : PreservesFiniteLength Φ) (hΦx : PreservesFiniteLengthShortExact Φ)
    (hΨl : PreservesFiniteLength Ψ) (hΨx : PreservesFiniteLengthShortExact Ψ) :
    map Φ hΦl hΦx = map Ψ hΨl hΨx := by
  apply hom_ext_object R G
  intro A
  rw [map_ofObject, map_ofObject]
  exact ofObject_eq_of_iso (e.app A.val)

end FiniteLengthGrothendieckGroup
end Langlands.SmoothRep

namespace Langlands.GeneralLinear.BlockShape

open SmoothRep

variable {n : ℕ} (B : BlockShape n) (F : Type uF) [Field F] [TopologicalSpace F]

/-- A functor from actual product-Levi to actual `GL_n(F)` representations, both
with saturated carriers `Type (max uF uV)`, induces a map of the published
specialized finite-length Grothendieck groups. -/
def finiteLengthMapToGeneralLinear
    (Φ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F))
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    B.FiniteLengthGrothendieckGroup.{uV, uF} F →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F :=
  FiniteLengthGrothendieckGroup.map Φ hl hx

theorem finiteLengthMapToGeneralLinear_finiteLengthClass
    (Φ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F))
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F)) (hA : A.HasFiniteLength) :
    B.finiteLengthMapToGeneralLinear F Φ hl hx (B.finiteLengthClass F A hA) =
      GeneralLinear.finiteLengthClass n F (Φ.obj A) (hl A hA) :=
  FiniteLengthGrothendieckGroup.map_ofRepresentation Φ hl hx A hA

/-- A functor from actual `GL_n(F)` to actual product-Levi representations, both
with saturated carriers `Type (max uF uV)`, induces a map of the published
specialized finite-length Grothendieck groups. -/
def finiteLengthMapFromGeneralLinear
    (Φ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F))
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F :=
  FiniteLengthGrothendieckGroup.map Φ hl hx

theorem finiteLengthMapFromGeneralLinear_finiteLengthClass
    (Φ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F))
    (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F)) (hA : A.HasFiniteLength) :
    B.finiteLengthMapFromGeneralLinear F Φ hl hx (GeneralLinear.finiteLengthClass n F A hA) =
      B.finiteLengthClass F (Φ.obj A) (hl A hA) :=
  FiniteLengthGrothendieckGroup.map_ofRepresentation Φ hl hx A hA

end Langlands.GeneralLinear.BlockShape
