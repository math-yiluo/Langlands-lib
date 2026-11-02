import Langlands.Sheaf.Equivariant.SmoothDirectImage
import Langlands.Sheaf.Equivariant.ProperSmoothCompactSections
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Langlands.Sheaf.Equivariant.Limits
import Langlands.Cohomology.DivisibleSystem.LeftExact

/-!
# Smooth direct image and proper compact sections of `ℓ`-divisible systems

Harris 1999, §2 works with `ℓ`-divisible systems of sheaves `{F_m}` and their sections.
This module transports `ℓ`-divisible systems of smooth sheaves along a continuous
equivariant map `f : X → Y`, using the Library's smooth direct image
`SmoothDirectImage.functor f hf` and `DivisibleSystem.mapLeftExact`.

* `directImageSheaf_preservesLimitsOfShape`, `directImageSheaf_preservesFiniteLimits`,
  `smoothCoreflector_preservesFiniteLimits`, `directImageSheaf_additive` and
  `smoothDirectImage_preservesFiniteLimits`: the ordinary equivariant direct image, the
  smooth part and the smooth direct image preserve finite limits, and the ordinary direct
  image of module sheaves is additive.
* `smoothDirectImageSystem f hf T hT`: the smooth direct image of an `ℓ`-divisible system
  of smooth sheaves on `X`, an `ℓ`-divisible system on `Y`, given the explicit hypothesis
  `hT` that the smooth direct images of the projections `j` are epimorphisms;
  `smoothDirectImageSystemMap` on morphisms.
* `smoothDirectImageSystemInclusion`: the levelwise monic inclusion of the smooth direct
  image system into the full ordinary direct image system.
* `smoothDirectImageSystemIdIso` and `smoothDirectImageSystemCompMap`: the identity
  isomorphism and the comparison for composite maps, levelwise `SmoothDirectImage.idIso`
  and `SmoothDirectImage.compMap`, with the unit and associativity laws.
* `properCompactSectionsSystemMap f hf hp T ...`: for a proper `f`, the morphism from
  compact sections of the smooth direct image system to compact sections of `T`, levelwise
  `ProperSmoothCompactSections.natTrans`, with its identity and composition laws.

All epimorphism hypotheses on projections stay explicit; none is derived here.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Sheaf.Equivariant

section Limits

universe uX uG uA vA uJ vJ

variable {G : Type uG} [Group G] {X Y : Type uX} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [MulAction G Y] (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
  (A : Type uA) [Category.{vA} A]

/-- The ordinary equivariant direct image preserves every limit that exists in the
coefficients: forgetting the sheaf condition, it is precomposition with inverse images
of opens. -/
instance directImageSheaf_preservesLimitsOfShape (J : Type uJ) [Category.{vJ} J]
    [HasLimitsOfShape J A] : PreservesLimitsOfShape J (DirectImage.sheaf f hf A) := by
  have : PreservesLimitsOfShape J (DirectImage.presheaf f hf A) :=
    CategoryTheory.whiskeringLeft_preservesLimitsOfShape J (DirectImage.preimage f hf).op
  have : PreservesLimitsOfShape J (DirectImage.sheaf f hf A ⋙ toTransportPresheaf G Y A) :=
    inferInstanceAs
      (PreservesLimitsOfShape J (toTransportPresheaf G X A ⋙ DirectImage.presheaf f hf A))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (toTransportPresheaf G Y A)

/-- The ordinary equivariant direct image is left exact. -/
instance directImageSheaf_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (DirectImage.sheaf f hf A) :=
  ⟨fun _ _ _ => inferInstance⟩

end Limits

section Smooth

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The smooth part of an equivariant module sheaf preserves finite limits; it is a right
adjoint. -/
instance smoothCoreflector_preservesFiniteLimits :
    PreservesFiniteLimits (smoothCoreflector (G := G) (X := X) R) := by
  have := (smoothAdjunction (G := G) (X := X) R).rightAdjoint_preservesLimits
  infer_instance

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]
  [ContinuousConstSMul G Y] [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y] in
/-- The ordinary equivariant direct image of module sheaves is additive. -/
instance directImageSheaf_additive : (DirectImage.sheaf f hf (ModuleCat.{u} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Smooth direct image is left exact. -/
instance smoothDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (SmoothDirectImage.functor (R := R) f hf) := by
  dsimp only [SmoothDirectImage.functor]
  infer_instance

variable {ℓ : ℕ}

/-- Smooth direct image of an `ℓ`-divisible system of smooth sheaves on `X`, as an
`ℓ`-divisible system of smooth sheaves on `Y`, given that the smooth direct images of the
projections `j` are epimorphisms. -/
def smoothDirectImageSystem (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h))) :
    SmoothSheafDivisibleSystem R G Y ℓ :=
  T.mapLeftExact (SmoothDirectImage.functor f hf) hT

@[simp]
lemma smoothDirectImageSystem_tower (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h))) :
    (smoothDirectImageSystem f hf T hT).tower = T.tower ⋙ SmoothDirectImage.functor f hf :=
  rfl

@[simp]
lemma smoothDirectImageSystem_inclusion (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    {m' m : ℕ} (h : m' < m) :
    (smoothDirectImageSystem f hf T hT).inclusion h =
      (SmoothDirectImage.functor f hf).map (T.inclusion h) :=
  rfl

/-- Smooth direct image of a morphism of `ℓ`-divisible systems of smooth sheaves. -/
def smoothDirectImageSystemMap {T T' : SmoothSheafDivisibleSystem R G X ℓ} (a : T ⟶ T')
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T'.projection h))) :
    smoothDirectImageSystem f hf T hT ⟶ smoothDirectImageSystem f hf T' hT' :=
  mapLeftExactHom T (SmoothDirectImage.functor f hf) hT a hT'

@[simp]
lemma smoothDirectImageSystemMap_tower_app {T T' : SmoothSheafDivisibleSystem R G X ℓ}
    (a : T ⟶ T')
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T'.projection h))) (m : ℕᵒᵖ) :
    (smoothDirectImageSystemMap f hf a hT hT').tower.app m =
      (SmoothDirectImage.functor f hf).map (a.tower.app m) :=
  rfl

/-- The inclusion of the smooth direct image into the full ordinary direct image, as a
morphism of `ℓ`-divisible systems of ordinary equivariant sheaves on `Y`. The source is the
smooth direct image system regarded as a system of ordinary sheaves (the inclusion of
smooth sheaves is exact); the target needs its own hypothesis that the full direct images
of the projections `j` are epimorphisms. -/
def smoothDirectImageSystemInclusion (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
        DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        (T.projection h))) :
    (smoothDirectImageSystem f hf T hT).map (Langlands.Sheaf.Equivariant.smoothInclusion R G Y) ⟶
      T.mapLeftExact (Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
        DirectImage.sheaf f hf (ModuleCat.{u} R)) hT' :=
  ⟨Functor.whiskerLeft T.tower (SmoothDirectImage.inclusion f hf),
    fun h => (SmoothDirectImage.inclusion f hf).naturality (T.inclusion h)⟩

@[simp]
lemma smoothDirectImageSystemInclusion_tower_app (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
        DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        (T.projection h))) (m : ℕᵒᵖ) :
    (smoothDirectImageSystemInclusion f hf T hT hT').tower.app m =
      (SmoothDirectImage.inclusion f hf).app (T.tower.obj m) :=
  rfl

/-- Every level of the inclusion into the full direct image is a monomorphism. -/
instance mono_smoothDirectImageSystemInclusion_tower_app
    (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Langlands.Sheaf.Equivariant.smoothInclusion R G X ⋙
        DirectImage.sheaf f hf (ModuleCat.{u} R)).map
        (T.projection h))) (m : ℕᵒᵖ) :
    Mono ((smoothDirectImageSystemInclusion f hf T hT hT').tower.app m) :=
  SmoothDirectImage.mono_inclusion_app f hf (T.tower.obj m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] in
/-- Equivariance of the identity map. -/
lemma smoothSpatial_id_equivariant :
    ∀ (g : G) (x : X), (ContinuousMap.id X) (g • x) = g • (ContinuousMap.id X) x :=
  fun _ _ => rfl

omit [ContinuousConstSMul G Y] [HasStableNeighbourhoods G Y] in
/-- Along the identity, smooth direct images of the projections `j` are epimorphisms. -/
lemma epi_smoothDirectImage_id_map_projection (T : SmoothSheafDivisibleSystem R G X ℓ)
    {m' m : ℕ} (h : m' ≤ m) :
    Epi ((SmoothDirectImage.functor (R := R) (ContinuousMap.id X)
      (smoothSpatial_id_equivariant (G := G) (X := X))).map (T.projection h)) := by
  have := T.epi_projection h
  have : (SmoothDirectImage.functor (R := R) (ContinuousMap.id X)
      (smoothSpatial_id_equivariant (G := G) (X := X))).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (SmoothDirectImage.idIso (R := R) (G := G) (X := X))
  infer_instance

/-- Along the identity, smooth direct image of an `ℓ`-divisible system of smooth sheaves is
isomorphic to the system itself, levelwise by `SmoothDirectImage.idIso` (the unit of the
smooth-part adjunction). -/
def smoothDirectImageSystemIdIso (T : SmoothSheafDivisibleSystem R G X ℓ) :
    T ≅ smoothDirectImageSystem (ContinuousMap.id X)
      (smoothSpatial_id_equivariant (G := G) (X := X)) T
      (fun h => epi_smoothDirectImage_id_map_projection T h) where
  hom := ⟨Functor.whiskerLeft T.tower (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom,
    fun h => (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.naturality
      (T.inclusion h)⟩
  inv := ⟨Functor.whiskerLeft T.tower (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).inv,
    fun h => (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).inv.naturality
      (T.inclusion h)⟩
  hom_inv_id := by
    apply hom_ext
    apply NatTrans.ext
    funext m
    exact (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom_inv_id_app (T.tower.obj m)
  inv_hom_id := by
    apply hom_ext
    apply NatTrans.ext
    funext m
    exact (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).inv_hom_id_app (T.tower.obj m)

@[simp]
lemma smoothDirectImageSystemIdIso_hom_tower_app (T : SmoothSheafDivisibleSystem R G X ℓ)
    (m : ℕᵒᵖ) :
    (smoothDirectImageSystemIdIso T).hom.tower.app m =
      (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app (T.tower.obj m) :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]
  [ContinuousConstSMul G Y] [ContinuousConstSMul G Z] [HasStableNeighbourhoods G X]
  [HasStableNeighbourhoods G Y] [HasStableNeighbourhoods G Z] in
include hf in
/-- Equivariance of a composite of equivariant maps. -/
lemma smoothSpatial_comp_equivariant (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) :
    ∀ (k : G) (x : X), (g.comp f) (k • x) = k • (g.comp f) x := fun k x => by
  change g (f (k • x)) = k • g (f x)
  rw [hf, hg]

/-- Comparison from the iterated smooth direct image of an `ℓ`-divisible system of smooth
sheaves to its smooth direct image along the composite map, levelwise
`SmoothDirectImage.compMap`. Each of the three systems carries its own hypothesis that the
images of the projections `j` are epimorphisms. -/
def smoothDirectImageSystemCompMap (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) g hg).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hT'' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) (g.comp f)
        (smoothSpatial_comp_equivariant f hf g hg)).map (T.projection h))) :
    smoothDirectImageSystem g hg (smoothDirectImageSystem f hf T hT) hT' ⟶
      smoothDirectImageSystem (g.comp f) (smoothSpatial_comp_equivariant f hf g hg) T hT'' :=
  ⟨Functor.whiskerLeft T.tower (SmoothDirectImage.compMap (R := R) f hf g hg),
    fun h => (SmoothDirectImage.compMap (R := R) f hf g hg).naturality (T.inclusion h)⟩

@[simp]
lemma smoothDirectImageSystemCompMap_tower_app (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) g hg).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hT'' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) (g.comp f)
        (smoothSpatial_comp_equivariant f hf g hg)).map (T.projection h))) (m : ℕᵒᵖ) :
    (smoothDirectImageSystemCompMap f hf g hg T hT hT' hT'').tower.app m =
      (SmoothDirectImage.compMap (R := R) f hf g hg).app (T.tower.obj m) :=
  rfl

/-- Unit law at the level of systems: inserting the identity before `f`. -/
theorem smoothDirectImageSystemCompMap_id_left (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map
        ((smoothDirectImageSystem (ContinuousMap.id X)
          (smoothSpatial_id_equivariant (G := G) (X := X)) T
          (fun h => epi_smoothDirectImage_id_map_projection T h)).projection h))) :
    smoothDirectImageSystemMap f hf (smoothDirectImageSystemIdIso T).hom hT hT' ≫
        smoothDirectImageSystemCompMap (ContinuousMap.id X)
          (smoothSpatial_id_equivariant (G := G) (X := X)) f hf T
          (fun h => epi_smoothDirectImage_id_map_projection T h) hT' hT =
      𝟙 _ := by
  apply hom_ext
  apply NatTrans.ext
  funext m
  exact SmoothDirectImage.compMap_id_left f hf (T.tower.obj m)

/-- Unit law at the level of systems: inserting the identity after `f`. -/
theorem smoothDirectImageSystemCompMap_id_right (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h))) :
    (smoothDirectImageSystemIdIso (smoothDirectImageSystem f hf T hT)).hom ≫
        smoothDirectImageSystemCompMap f hf (ContinuousMap.id Y)
          (smoothSpatial_id_equivariant (G := G) (X := Y)) T hT
          (fun h => epi_smoothDirectImage_id_map_projection _ h) hT =
      𝟙 _ := by
  apply hom_ext
  apply NatTrans.ext
  funext m
  exact SmoothDirectImage.compMap_id_right f hf (T.tower.obj m)

/-- Associativity at the level of systems: the two comparisons from three iterated smooth
direct images agree. -/
theorem smoothDirectImageSystemCompMap_assoc {W : Type u} [TopologicalSpace W]
    [MulAction G W] [ContinuousConstSMul G W] [HasStableNeighbourhoods G W]
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (e : C(Z, W)) (he : ∀ (k : G) (z : Z), e (k • z) = k • e z)
    (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT₁ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) g hg).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hT₂ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) e he).map
        ((smoothDirectImageSystem g hg (smoothDirectImageSystem f hf T hT) hT₁).projection h)))
    (hT₃ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) (g.comp f)
        (smoothSpatial_comp_equivariant f hf g hg)).map (T.projection h)))
    (hT₄ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) e he).map
        ((smoothDirectImageSystem (g.comp f) (smoothSpatial_comp_equivariant f hf g hg) T
          hT₃).projection h)))
    (hT₅ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) (e.comp g)
        (smoothSpatial_comp_equivariant g hg e he)).map
          ((smoothDirectImageSystem f hf T hT).projection h)))
    (hT₆ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) ((e.comp g).comp f)
        (smoothSpatial_comp_equivariant f hf (e.comp g)
          (smoothSpatial_comp_equivariant g hg e he))).map (T.projection h))) :
    smoothDirectImageSystemMap e he (smoothDirectImageSystemCompMap f hf g hg T hT hT₁ hT₃)
          hT₂ hT₄ ≫
        smoothDirectImageSystemCompMap (g.comp f) (smoothSpatial_comp_equivariant f hf g hg)
          e he T hT₃ hT₄ hT₆ =
      smoothDirectImageSystemCompMap g hg e he (smoothDirectImageSystem f hf T hT) hT₁ hT₂
          hT₅ ≫
        smoothDirectImageSystemCompMap f hf (e.comp g)
          (smoothSpatial_comp_equivariant g hg e he) T hT hT₅ hT₆ := by
  apply hom_ext
  apply NatTrans.ext
  funext m
  exact SmoothDirectImage.compMap_assoc f hf g hg e he (T.tower.obj m)

/-- Proper pullback on compact sections at the level of `ℓ`-divisible systems: for a proper
equivariant map `f`, the morphism from compact sections of the smooth direct image system on
`Y` to compact sections of the original system on `X`, levelwise
`ProperSmoothCompactSections.natTrans`. Both compact-section systems carry their own
hypothesis that compact sections of the projections `j` are epimorphisms. -/
def properCompactSectionsSystemMap (hp : IsProperMap f)
    (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hc : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G Y).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hc' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map (T.projection h))) :
    compactSectionsSystem (smoothDirectImageSystem f hf T hT) hc ⟶
      compactSectionsSystem T hc' :=
  ⟨Functor.whiskerLeft T.tower (ProperSmoothCompactSections.natTrans f hf hp),
    fun h => (ProperSmoothCompactSections.natTrans f hf hp).naturality (T.inclusion h)⟩

@[simp]
lemma properCompactSectionsSystemMap_tower_app (hp : IsProperMap f)
    (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hc : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G Y).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hc' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map (T.projection h))) (m : ℕᵒᵖ) :
    (properCompactSectionsSystemMap f hf hp T hT hc hc').tower.app m =
      (ProperSmoothCompactSections.natTrans f hf hp).app (T.tower.obj m) :=
  rfl

/-- Along the identity, proper pullback on compact sections of systems is inverse to compact
sections of `smoothDirectImageSystemIdIso`. -/
theorem properCompactSectionsSystemMap_id (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hc : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothDirectImageSystem (ContinuousMap.id X)
          (smoothSpatial_id_equivariant (G := G) (X := X)) T
          (fun h => epi_smoothDirectImage_id_map_projection T h)).projection h)))
    (hc' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map (T.projection h))) :
    mapLeftExactHom T (smoothSheafCompactSections R G X) hc'
          (smoothDirectImageSystemIdIso T).hom hc ≫
        properCompactSectionsSystemMap (ContinuousMap.id X)
          (smoothSpatial_id_equivariant (G := G) (X := X)) isProperMap_id T
          (fun h => epi_smoothDirectImage_id_map_projection T h) hc hc' =
      𝟙 _ := by
  apply hom_ext
  apply NatTrans.ext
  funext m
  exact ProperSmoothCompactSections.natTrans_id (T.tower.obj m)

/-- Proper pullback on compact sections of systems is compatible with
`smoothDirectImageSystemCompMap`. -/
theorem properCompactSectionsSystemMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) (hp : IsProperMap f) (hq : IsProperMap g)
    (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) f hf).map (T.projection h)))
    (hT' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) g hg).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hT'' : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothDirectImage.functor (R := R) (g.comp f)
        (smoothSpatial_comp_equivariant f hf g hg)).map (T.projection h)))
    (hc₀ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map (T.projection h)))
    (hc₁ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G Y).map
        ((smoothDirectImageSystem f hf T hT).projection h)))
    (hc₂ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G Z).map
        ((smoothDirectImageSystem g hg (smoothDirectImageSystem f hf T hT) hT').projection h)))
    (hc₃ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G Z).map
        ((smoothDirectImageSystem (g.comp f) (smoothSpatial_comp_equivariant f hf g hg) T
          hT'').projection h))) :
    mapLeftExactHom (smoothDirectImageSystem g hg (smoothDirectImageSystem f hf T hT) hT')
          (smoothSheafCompactSections R G Z) hc₂
          (smoothDirectImageSystemCompMap f hf g hg T hT hT' hT'') hc₃ ≫
        properCompactSectionsSystemMap (g.comp f) (smoothSpatial_comp_equivariant f hf g hg)
          (hq.comp hp) T hT'' hc₃ hc₀ =
      properCompactSectionsSystemMap g hg hq (smoothDirectImageSystem f hf T hT) hT' hc₂ hc₁ ≫
        properCompactSectionsSystemMap f hf hp T hT hc₁ hc₀ := by
  apply hom_ext
  apply NatTrans.ext
  funext m
  exact ProperSmoothCompactSections.natTrans_comp f hf g hg hp hq (T.tower.obj m)

end Smooth

end Langlands.Cohomology.DivisibleSystem
