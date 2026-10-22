import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Langlands.Representation.Category.Abelian
import Langlands.Sheaf.Equivariant.SmoothAbelian

/-!
# `ℓ`-divisible systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §2, p.304,
equation (2.1): an `ℓ`-divisible system is a family `T m`, `m ≥ 1`, killed by `ℓ ^ m`,
free over `ℤ / ℓ ^ m`, with maps `i : T m' ⟶ T m` and `j : T m ⟶ T (m - m')` for
`m > m'`, such that `i` identifies `T m'` with the `ℓ ^ m'`-torsion of `T m` and
`0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0` is exact.

The maps `j` form an inverse system indexed by `ℕᵒᵖ`, and `T 0` is the zero object.
Freeness is rendered by exactness of `T m ⟶ T m ⟶ T m` given by `ℓ ^ a` and `ℓ ^ b`
for `a + b = m`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u' w

section PowSMul

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Multiplication by `ℓ ^ m` on an object of a preadditive category. -/
def powSMul (ℓ m : ℕ) (X : C) : X ⟶ X :=
  (ℓ ^ m) • 𝟙 X

lemma comp_powSMul (ℓ m : ℕ) {X Y : C} (f : X ⟶ Y) :
    f ≫ powSMul ℓ m Y = powSMul ℓ m X ≫ f := by
  simp only [powSMul, Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.id_comp]

lemma powSMul_comp_powSMul (ℓ a b : ℕ) (X : C) :
    powSMul ℓ a X ≫ powSMul ℓ b X = powSMul ℓ (a + b) X := by
  simp only [powSMul, Preadditive.comp_nsmul, Category.comp_id]
  rw [smul_smul, ← pow_add, add_comm]

lemma powSMul_zero (ℓ : ℕ) (X : C) : powSMul ℓ 0 X = 𝟙 X := by
  simp [powSMul]

lemma map_powSMul {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (ℓ m : ℕ) (X : C) : F.map (powSMul ℓ m X) = powSMul ℓ m (F.obj X) := by
  simp [powSMul, F.map_nsmul]

end PowSMul

lemma shortComplex_exact_congr {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ : C} {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} {w : f ≫ g = 0} {w' : f' ≫ g' = 0}
    (hf : f = f') (hg : g = g') (h : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk f' g' w').Exact := by
  subst hf hg
  exact h

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- An `ℓ`-divisible system in an abelian category (Harris 1999, (2.1)). The transition
maps `j : T m ⟶ T (m - m')` are the maps of the functor `tower`. -/
structure DivisibleSystem (ℓ : ℕ) where
  /-- The objects `T m` together with the maps `j`. -/
  tower : ℕᵒᵖ ⥤ C
  /-- The map `i : T m' ⟶ T m` for `m' < m`. -/
  inclusion {m' m : ℕ} (h : m' < m) : tower.obj (op m') ⟶ tower.obj (op m)
  powSMul_eq_zero (m : ℕ) : powSMul ℓ m (tower.obj (op m)) = 0
  inclusion_comp {m' m : ℕ} (h : m' < m) :
    inclusion h ≫ tower.map (homOfLE (Nat.sub_le m m')).op = 0
  shortExact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (inclusion h) (tower.map (homOfLE (Nat.sub_le m m')).op)
      (inclusion_comp h)).ShortExact
  torsion_exact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (inclusion h) (powSMul ℓ m' (tower.obj (op m)))
      (by rw [comp_powSMul, powSMul_eq_zero, zero_comp])).Exact
  flat (a b : ℕ) :
    (ShortComplex.mk (powSMul ℓ a (tower.obj (op (a + b))))
      (powSMul ℓ b (tower.obj (op (a + b))))
      (by rw [powSMul_comp_powSMul, powSMul_eq_zero])).Exact

namespace DivisibleSystem

variable {C} {ℓ : ℕ}

section Basic

variable (T : DivisibleSystem C ℓ)

/-- The object `T m`. -/
abbrev obj (m : ℕ) : C := T.tower.obj (op m)

/-- The transition map `T m ⟶ T m'` for `m' ≤ m`. -/
abbrev projection {m' m : ℕ} (h : m' ≤ m) : T.obj m ⟶ T.obj m' :=
  T.tower.map (homOfLE h).op

lemma isZero_obj_zero : IsZero (T.obj 0) := by
  rw [IsZero.iff_id_eq_zero, ← powSMul_zero ℓ]
  exact T.powSMul_eq_zero 0

instance mono_inclusion {m' m : ℕ} (h : m' < m) : Mono (T.inclusion h) :=
  (T.shortExact h).mono_f

lemma epi_projection {m' m : ℕ} (h : m' ≤ m) : Epi (T.projection h) := by
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · exact ⟨fun _ _ _ => (T.isZero_obj_zero).eq_of_src _ _⟩
  have hlt : m - m' < m := by omega
  have key : Epi (T.projection (Nat.sub_le m (m - m'))) := (T.shortExact hlt).epi_g
  have aux : ∀ (n : ℕ) (hn : n ≤ m), n = m - (m - m') → Epi (T.projection hn) := by
    rintro n hn rfl
    exact key
  exact aux m' h (by omega)

/-- `i : T m' ⟶ T m` is a kernel of multiplication by `ℓ ^ m'` on `T m`. -/
def inclusionIsKernel {m' m : ℕ} (h : m' < m) :
    IsLimit (KernelFork.ofι (T.inclusion h)
      (by rw [comp_powSMul, T.powSMul_eq_zero, zero_comp])) :=
  (T.torsion_exact h).fIsKernel

/-- `j : T m ⟶ T (m - m')` is a cokernel of `i : T m' ⟶ T m`. -/
def projectionIsCokernel {m' m : ℕ} (h : m' < m) :
    IsColimit (CokernelCofork.ofπ (T.projection (Nat.sub_le m m')) (T.inclusion_comp h)) :=
  (T.shortExact h).gIsCokernel

end Basic

/-- A morphism of `ℓ`-divisible systems: a morphism of inverse systems commuting with the
maps `i`. -/
@[ext]
structure Hom (T T' : DivisibleSystem C ℓ) where
  /-- The underlying morphism of inverse systems. -/
  tower : T.tower ⟶ T'.tower
  comm {m' m : ℕ} (h : m' < m) :
    T.inclusion h ≫ tower.app (op m) = tower.app (op m') ≫ T'.inclusion h

instance : Category (DivisibleSystem C ℓ) where
  Hom := Hom
  id T := ⟨𝟙 T.tower, fun _ => by simp⟩
  comp f g := ⟨f.tower ≫ g.tower, fun h => by
    simp only [NatTrans.comp_app]
    rw [reassoc_of% f.comm h, g.comm h, Category.assoc]⟩

@[ext]
lemma hom_ext {T T' : DivisibleSystem C ℓ} {f g : T ⟶ T'} (h : f.tower = g.tower) : f = g :=
  Hom.ext h

@[simp]
lemma id_tower (T : DivisibleSystem C ℓ) : Hom.tower (𝟙 T) = 𝟙 T.tower :=
  rfl

@[simp]
lemma comp_tower {T T' T'' : DivisibleSystem C ℓ} (f : T ⟶ T') (g : T' ⟶ T'') :
    Hom.tower (f ≫ g) = f.tower ≫ g.tower :=
  rfl

variable (C ℓ) in
/-- The underlying inverse system. -/
@[simps]
def forget : DivisibleSystem C ℓ ⥤ (ℕᵒᵖ ⥤ C) where
  obj T := T.tower
  map f := f.tower

instance : (forget C ℓ).Faithful where
  map_injective h := hom_ext h

section Map

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An additive functor preserving finite limits and finite colimits carries an
`ℓ`-divisible system to an `ℓ`-divisible system. -/
@[simps tower]
def map (T : DivisibleSystem C ℓ) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : DivisibleSystem D ℓ where
  tower := T.tower ⋙ F
  inclusion h := F.map (T.inclusion h)
  powSMul_eq_zero m := by
    rw [Functor.comp_obj, ← map_powSMul, T.powSMul_eq_zero, F.map_zero]
  inclusion_comp h := by
    rw [Functor.comp_map, ← F.map_comp, T.inclusion_comp, F.map_zero]
  shortExact h := (T.shortExact h).map_of_exact F
  torsion_exact h := shortComplex_exact_congr rfl (map_powSMul F _ _ _)
    ((T.torsion_exact h).map F)
  flat a b := shortComplex_exact_congr (map_powSMul F _ _ _) (map_powSMul F _ _ _)
    ((T.flat a b).map F)

@[simp]
lemma map_inclusion (T : DivisibleSystem C ℓ) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {m' m : ℕ} (h : m' < m) :
    (T.map F).inclusion h = F.map (T.inclusion h) :=
  rfl

variable (C ℓ) in
/-- `map` as a functor on `ℓ`-divisible systems. -/
@[simps obj]
def mapFunctor (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ where
  obj T := T.map F
  map f := ⟨Functor.whiskerRight f.tower F, fun h => by
    exact (F.map_comp _ _).symm.trans ((congrArg F.map (f.comm h)).trans (F.map_comp _ _))⟩

/-- A natural transformation between exact additive functors induces a morphism of the
image `ℓ`-divisible systems. -/
@[simps tower]
def mapNatTrans (T : DivisibleSystem C ℓ) {F G : C ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ⟶ G) :
    T.map F ⟶ T.map G :=
  ⟨Functor.whiskerLeft T.tower α, fun h => α.naturality (T.inclusion h)⟩

end Map

section Complexes

variable {ι : Type*} {c : ComplexShape ι}

/-- The `ℓ`-divisible system of degree `n` terms of an `ℓ`-divisible system of complexes. -/
abbrev degree (T : DivisibleSystem (HomologicalComplex C c) ℓ) (n : ι) : DivisibleSystem C ℓ :=
  T.map (HomologicalComplex.eval C c n)

end Complexes

end DivisibleSystem

/-- Harris's `ℓ`-divisible systems of `G`-equivariant smooth sheaves over `X` (Harris 1999,
(2.1), with Berkovich's discrete sheaves as smooth sheaves). -/
abbrev SmoothSheafDivisibleSystem (R : Type u) [CommRing R] (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (X : Type u) [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [Sheaf.Equivariant.HasStableNeighbourhoods G X]
    (ℓ : ℕ) :=
  DivisibleSystem (Sheaf.Equivariant.SmoothTopologicalSheaf R G X) ℓ

/-- `ℓ`-divisible systems of cochain complexes of smooth representations (Harris 1999,
p.306, the systems `C_m`). -/
abbrev SmoothRepComplexDivisibleSystem (R : Type u) [CommRing R] (G : Type v) [Group G]
    [TopologicalSpace G] (ℓ : ℕ) :=
  DivisibleSystem (CochainComplex (SmoothRep.{u, v, w} R G) ℤ) ℓ

end Langlands.Cohomology
