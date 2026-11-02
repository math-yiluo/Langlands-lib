import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV uS uH uW

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  {S : Type uS} {H : Type uH} [CommRing S] [Group H] [TopologicalSpace H]

/-- An actual smooth isomorphism preserves finite group-algebra length. -/
theorem hasFiniteLength_of_iso {A B : SmoothRep.{uR, uG, uV} R G}
    (e : A ≅ B) (hA : A.HasFiniteLength) : B.HasFiniteLength :=
  hA.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom e.hom))
    (equivOfIso e).toLinearEquiv.surjective

/-- Actual short exactness transfers through three smooth isomorphisms and
commuting squares. -/
theorem isShortExact_of_iso
    {A B C A' B' C' : SmoothRep.{uR, uG, uV} R G}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C')
    {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    (hfcomm : f ≫ eB.hom = eA.hom ≫ f')
    (hgcomm : g ≫ eC.hom = eB.hom ≫ g')
    (h : IsShortExact (hom f) (hom g)) :
    IsShortExact (hom f') (hom g') := by
  have hf (a : A) : hom eB.hom (hom f a) = hom f' (hom eA.hom a) :=
    congrArg (fun k : A ⟶ B' => hom k a) hfcomm
  have hg (b : B) : hom eC.hom (hom g b) = hom g' (hom eB.hom b) :=
    congrArg (fun k : B ⟶ C' => hom k b) hgcomm
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (equivOfIso eA).toLinearEquiv.surjective x
    obtain ⟨b, rfl⟩ := (equivOfIso eA).toLinearEquiv.surjective y
    apply congrArg (hom eA.hom)
    apply h.1
    apply (equivOfIso eB).toLinearEquiv.injective
    change hom eB.hom (hom f a) = hom eB.hom (hom f b)
    rw [hf, hf]
    exact hxy
  · intro z
    obtain ⟨c, rfl⟩ := (equivOfIso eC).toLinearEquiv.surjective z
    obtain ⟨b, hb⟩ := h.2.1 c
    refine ⟨hom eB.hom b, ?_⟩
    rw [← hg, hb]
    rfl
  · ext b'
    constructor
    · rintro ⟨a', rfl⟩
      obtain ⟨a, rfl⟩ := (equivOfIso eA).toLinearEquiv.surjective a'
      change hom g' (hom f' (hom eA.hom a)) = 0
      rw [← hf, ← hg]
      have hzero : hom g (hom f a) = 0 := by
        have hm : hom f a ∈ LinearMap.range (hom f).toLinearMap := ⟨a, rfl⟩
        rwa [h.2.2, LinearMap.mem_ker] at hm
      rw [hzero, map_zero]
    · intro hb'
      obtain ⟨b, rfl⟩ := (equivOfIso eB).toLinearEquiv.surjective b'
      have hb : hom g b = 0 := by
        apply (equivOfIso eC).toLinearEquiv.injective
        change hom eC.hom (hom g b) = hom eC.hom 0
        rw [hg, map_zero]
        exact hb'
      have hbrange : b ∈ LinearMap.range (hom f).toLinearMap := by
        rw [h.2.2, LinearMap.mem_ker]
        exact hb
      obtain ⟨a, ha⟩ := hbrange
      change hom f a = b at ha
      refine ⟨hom eA.hom a, ?_⟩
      change hom f' (hom eA.hom a) = hom eB.hom b
      rw [← hf, ha]

/-- Finite-length preservation transfers along a natural isomorphism. -/
theorem PreservesFiniteLength.of_iso
    {Φ Ψ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    (hΦ : PreservesFiniteLength Φ) (e : Φ ≅ Ψ) : PreservesFiniteLength Ψ :=
  fun A hA => hasFiniteLength_of_iso (e.app A) (hΦ A hA)

/-- Short-exact preservation transfers along a natural isomorphism. -/
theorem PreservesFiniteLengthShortExact.of_iso
    {Φ Ψ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    (hΦ : PreservesFiniteLengthShortExact Φ) (e : Φ ≅ Ψ) :
    PreservesFiniteLengthShortExact Ψ := by
  intro A B C f g hA hB hC h
  exact isShortExact_of_iso (e.app A) (e.app B) (e.app C)
    (e.hom.naturality f) (e.hom.naturality g) (hΦ f g hA hB hC h)

namespace FiniteLengthGrothendieckGroup

/-- The existing exact-K0 map with preservation supplied by a naturally
isomorphic functor. -/
def mapOfIso
    {Φ Ψ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    (e : Φ ≅ Ψ) (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uS, uH, uW} S H :=
  map Ψ (hl.of_iso e) (hx.of_iso e)

/-- Transport of the preservation proofs leaves the whole exact-K0 map unchanged. -/
theorem mapOfIso_eq
    {Φ Ψ : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uS, uH, uW} S H}
    (e : Φ ≅ Ψ) (hl : PreservesFiniteLength Φ) (hx : PreservesFiniteLengthShortExact Φ) :
    mapOfIso e hl hx = map Φ hl hx :=
  (map_eq_of_iso e hl hx (hl.of_iso e) (hx.of_iso e)).symm

end FiniteLengthGrothendieckGroup
end Langlands.SmoothRep
