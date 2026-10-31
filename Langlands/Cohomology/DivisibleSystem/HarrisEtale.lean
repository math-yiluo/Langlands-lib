import Langlands.Cohomology.DivisibleSystem.ReductionLattice
import Langlands.Cohomology.DivisibleSystem.LeftExact
import Langlands.Shimura.Coefficients.HarrisEtaleCoefficients
import Langlands.Shimura.Coefficients.EtaleExact

/-!
# Harris's étale coefficient sheaves as `ℓ`-divisible systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.311: "The
constant étale sheaf `𝓛̃_m` on `S(GG, X_{n-1})_{K(N,m)}` descends to a lisse étale sheaf,
still denoted `𝓛̃_m`, on `S(GG, X_{n-1})_{K(N)}`", and "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`.
Then `𝓛_m` forms an inverse system of `𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a
lisse `ℓ`-adic sheaf"; §2, p.304, (2.1): `ℓ`-divisible systems.

The published `harrisEtaleCoefficientSystem` associates the reductions `𝓛 / ℓ ^ m 𝓛` of
Harris's lattice, with their actions of the congruence quotients of the level `U`, to a
compatible diagram `Y` of finite geometric étale torsors over a scheme `X`. It is an inverse
system of étale sheaves, with the maps `j` only. This module constructs the maps `i` and proves
that these sheaves form an `ℓ`-divisible system:

* `ofTowerIso`, `ofTowerIso_inclusion`, `isoOfTowerIso`: transport of an `ℓ`-divisible system
  along an isomorphism of inverse systems;
* `powSMul_action_hom`, `action_exact_of_map`, `action_shortExact_of_map`: (short) exactness of
  short complexes of actions is detected on the underlying objects;
* `EquivariantStructure` with `diagram`, `inclusionHom`, `powSMul_eq_zero`, `shortComplex`,
  `torsionShortComplex`, `flatShortComplex` and their exactness: compatible actions of an
  inverse system of groups `D` on an `ℓ`-divisible system `T`, for which the maps `i` and `j`
  are equivariant, and the sequences defining `ℓ`-divisible systems as short complexes of
  representations of `D m`;
* `etaleInclusion`, `etale_powSMul_eq_zero`, `etaleInclusion_comp`, `etale_shortExact`,
  `etale_torsion_exact`, `etale_flat`, `etaleSystem`: for such a structure on a system of
  modules and finite geometric étale torsors `Y m` under `D m`, the published associated
  étale sheaves form an `ℓ`-divisible system;
* `harrisTorsionDivisibleSystem`, `harrisEquivariantStructure`, `harrisEtaleDivisibleSystem`,
  `harrisEtaleSectionsDivisibleSystem`: Harris's case. Their inverse systems are the published
  `harrisCoefficientDiagram`, `harrisEtaleCoefficientSystem` and `harrisEtaleSectionsSystem`;
  the sections system needs the explicit hypothesis that global sections of the maps `j` are
  epimorphisms.

Harris does not state that the sheaves `𝓛̃_m` form an `ℓ`-divisible system; the statements and
proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w u'

namespace DivisibleSystem

section TowerIso

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- Transport of an `ℓ`-divisible system along an isomorphism of inverse systems: the maps
`i` are conjugated by the isomorphism. -/
@[simps tower]
def ofTowerIso (T : DivisibleSystem C ℓ) {F : ℕᵒᵖ ⥤ C} (e : T.tower ≅ F) :
    DivisibleSystem C ℓ where
  tower := F
  inclusion h := e.inv.app _ ≫ T.inclusion h ≫ e.hom.app _
  powSMul_eq_zero m := by
    have key := comp_powSMul ℓ m (e.hom.app (op m))
    rw [T.powSMul_eq_zero, zero_comp] at key
    calc powSMul ℓ m (F.obj (op m))
        = e.inv.app (op m) ≫ e.hom.app (op m) ≫ powSMul ℓ m (F.obj (op m)) :=
          (Iso.inv_hom_id_app_assoc e (op m) _).symm
      _ = 0 := by rw [key, comp_zero]
  inclusion_comp {m' m} h := by
    rw [Category.assoc, Category.assoc, ← e.hom.naturality, ← Category.assoc (T.inclusion h),
      T.inclusion_comp, zero_comp, comp_zero]
  shortExact {m' m} h := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (e.app _) (e.app _) (e.app _)
      (by simp) (e.hom.naturality _).symm) (T.shortExact h)
  torsion_exact {m' m} h := ShortComplex.exact_of_iso
    (ShortComplex.isoMk (e.app _) (e.app _) (e.app _)
      (by simp) (comp_powSMul ℓ m' _)) (T.torsion_exact h)
  flat a b := ShortComplex.exact_of_iso
    (ShortComplex.isoMk (e.app _) (e.app _) (e.app _)
      (comp_powSMul ℓ a _) (comp_powSMul ℓ b _)) (T.flat a b)

lemma ofTowerIso_inclusion (T : DivisibleSystem C ℓ) {F : ℕᵒᵖ ⥤ C} (e : T.tower ≅ F)
    {m' m : ℕ} (h : m' < m) :
    (T.ofTowerIso e).inclusion h = e.inv.app _ ≫ T.inclusion h ≫ e.hom.app _ :=
  rfl

/-- An `ℓ`-divisible system is isomorphic to its transport along an isomorphism of inverse
systems. -/
@[simps]
def isoOfTowerIso (T : DivisibleSystem C ℓ) {F : ℕᵒᵖ ⥤ C} (e : T.tower ≅ F) :
    T ≅ T.ofTowerIso e where
  hom := ⟨e.hom, fun _ => (Iso.hom_inv_id_app_assoc e _ _).symm⟩
  inv := ⟨e.inv, fun h => (Category.assoc _ _ _).trans (congrArg (e.inv.app _ ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (T.inclusion h ≫ ·) (e.hom_inv_id_app _)).trans
      (Category.comp_id _))))⟩
  hom_inv_id := hom_ext ((comp_tower _ _).trans (e.hom_inv_id.trans (id_tower T).symm))
  inv_hom_id := hom_ext ((comp_tower _ _).trans (e.inv_hom_id.trans (id_tower (T.ofTowerIso e)).symm))

end TowerIso

section Action

variable {V : Type u} [Category.{v} V] [Abelian V] {G : Type w} [Group G]

/-- Multiplication by `ℓ ^ m` on an action is multiplication by `ℓ ^ m` on the underlying
object. -/
lemma powSMul_action_hom (ℓ m : ℕ) (N : Action V G) : (powSMul ℓ m N).hom = powSMul ℓ m N.V :=
  map_powSMul (Action.forget V G) ℓ m N

/-- A short complex of actions is exact when its underlying short complex is. -/
lemma action_exact_of_map (S : ShortComplex (Action V G))
    (h : (S.map (Action.forget V G)).Exact) : S.Exact :=
  (S.exact_map_iff_of_faithful (Action.forget V G)).mp h

/-- A short complex of actions is short exact when its underlying short complex is. -/
lemma action_shortExact_of_map (S : ShortComplex (Action V G))
    (h : (S.map (Action.forget V G)).ShortExact) : S.ShortExact where
  exact := action_exact_of_map S h.exact
  mono_f := (Action.forget V G).mono_of_mono_map h.mono_f
  epi_g := (Action.forget V G).epi_of_epi_map h.epi_g

end Action

section Equivariant

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- Compatible actions of an inverse system of groups `D` on an `ℓ`-divisible system: the
group `D m` acts on `T m`, the maps `j` are equivariant along the maps `D m ⟶ D m'`, and so
are the maps `i : T m' ⟶ T m` when `D m` acts on `T m'` through `D m ⟶ D m'`. -/
structure EquivariantStructure (T : DivisibleSystem C ℓ) (D : ℕᵒᵖ ⥤ GrpCat.{u'}) where
  /-- The action of `D m` on `T m`. -/
  act (n : ℕᵒᵖ) : D.obj n →* End (T.tower.obj n)
  comm {i j : ℕᵒᵖ} (f : i ⟶ j) (g : D.obj i) :
    act i g ≫ T.tower.map f = T.tower.map f ≫ act j ((D.map f).hom g)
  inclusion_comm {m' m : ℕ} (h : m' < m) (g : D.obj (op m)) :
    act (op m') ((D.map (homOfLE h.le).op).hom g) ≫ T.inclusion h = T.inclusion h ≫ act (op m) g

namespace EquivariantStructure

variable {T : DivisibleSystem C ℓ} {D : ℕᵒᵖ ⥤ GrpCat.{u'}} (A : EquivariantStructure T D)

/-- The inverse system `T` with its actions, as an equivariant diagram. -/
def diagram : EquivariantDiagram D C where
  obj := T.tower
  ρ := A.act
  comm := A.comm

/-- The map `i : T m' ⟶ T m` as a morphism of representations of `D m`, which acts on
`T m'` through `D m ⟶ D m'`. -/
def inclusionHom {m' m : ℕ} (h : m' < m) :
    (Action.res C (D.map (homOfLE h.le).op).hom).obj (A.diagram.action (op m')) ⟶
      A.diagram.action (op m) where
  hom := T.inclusion h
  comm g := A.inclusion_comm h g

@[simp]
lemma inclusionHom_hom {m' m : ℕ} (h : m' < m) : (A.inclusionHom h).hom = T.inclusion h :=
  rfl

/-- `ℓ ^ m` is zero on the representation `T m` of `D m`. -/
lemma powSMul_eq_zero (m : ℕ) : powSMul ℓ m (A.diagram.action (op m)) = 0 := by
  apply Action.Hom.ext
  rw [powSMul_action_hom, Action.zero_hom]
  exact T.powSMul_eq_zero m

/-- The sequence `0 ⟶ T m' ⟶ T m ⟶ T (m - m') ⟶ 0` of (2.1) as a short complex of
representations of `D m`. -/
@[simps]
def shortComplex {m' m : ℕ} (h : m' < m) : ShortComplex (Action C (D.obj (op m))) :=
  ShortComplex.mk (A.inclusionHom h) (A.diagram.transition (homOfLE (Nat.sub_le m m')).op)
    (Action.Hom.ext (T.inclusion_comp h))

lemma shortComplex_shortExact {m' m : ℕ} (h : m' < m) : (A.shortComplex h).ShortExact :=
  action_shortExact_of_map _ (T.shortExact h)

/-- The torsion sequence `T m' ⟶ T m ⟶ T m`, the second map being `ℓ ^ m'`, as a short
complex of representations of `D m`. -/
@[simps]
def torsionShortComplex {m' m : ℕ} (h : m' < m) : ShortComplex (Action C (D.obj (op m))) :=
  ShortComplex.mk (A.inclusionHom h) (powSMul ℓ m' (A.diagram.action (op m)))
    (by
      apply Action.Hom.ext
      rw [Action.comp_hom, powSMul_action_hom, Action.zero_hom, comp_powSMul]
      exact (congrArg (· ≫ T.inclusion h) (T.powSMul_eq_zero m')).trans zero_comp)

lemma torsionShortComplex_exact {m' m : ℕ} (h : m' < m) : (A.torsionShortComplex h).Exact :=
  action_exact_of_map _
    (shortComplex_exact_congr rfl (powSMul_action_hom ℓ m' _).symm (T.torsion_exact h))

/-- The sequence `T (a + b) ⟶ T (a + b) ⟶ T (a + b)` given by `ℓ ^ a` and `ℓ ^ b`, as a
short complex of representations of `D (a + b)`. -/
@[simps]
def flatShortComplex (a b : ℕ) : ShortComplex (Action C (D.obj (op (a + b)))) :=
  ShortComplex.mk (powSMul ℓ a (A.diagram.action (op (a + b))))
    (powSMul ℓ b (A.diagram.action (op (a + b))))
    (by rw [powSMul_comp_powSMul, A.powSMul_eq_zero])

lemma flatShortComplex_exact (a b : ℕ) : (A.flatShortComplex a b).Exact :=
  action_exact_of_map _ (shortComplex_exact_congr (powSMul_action_hom ℓ a _).symm
    (powSMul_action_hom ℓ b _).symm (T.flat a b))

end EquivariantStructure

end Equivariant

section Etale

open Langlands.Shimura.Coefficients

variable (X : Scheme.{u}) {R : Type u} [CommRing R] {ℓ : ℕ}
variable {D : ℕᵒᵖ ⥤ GrpCat.{u}} (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable {T : DivisibleSystem (ModuleCat.{u} R) ℓ} (A : T.EquivariantStructure D)

namespace EquivariantStructure

/-- The étale map `i : 𝓛 m' ⟶ 𝓛 m`: the proved comparison of associated sheaves along the
cover map from level `m` to level `m'`, followed by the associated map of `i`. -/
def etaleInclusion {m' m : ℕ} (h : m' < m) :
    (etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op m') ⟶
      (etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op m) :=
  (etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op).hom.app A.diagram ≫
    (etaleAssociatedFunctor X (Y.action (op m))).map (A.inclusionHom h)

/-- `ℓ ^ m` is zero on the associated sheaf `𝓛 m`. -/
lemma etale_powSMul_eq_zero (m : ℕ) :
    powSMul ℓ m ((etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op m)) = 0 :=
  (map_powSMul (etaleAssociatedFunctor X (Y.action (op m))) ℓ m _).symm.trans
    ((congrArg (etaleAssociatedFunctor X (Y.action (op m))).map (A.powSMul_eq_zero m)).trans
      (Functor.map_zero _ _ _))

/-- The composite `𝓛 m' ⟶ 𝓛 m ⟶ 𝓛 (m - m')` of `i` and `j` is zero. -/
lemma etaleInclusion_comp {m' m : ℕ} (h : m' < m) :
    A.etaleInclusion X Y hY h ≫
      (etaleAssociatedVaryingSystem X Y hY A.diagram).map (homOfLE (Nat.sub_le m m')).op = 0 := by
  have key : (etaleAssociatedFunctor X (Y.action (op m))).map (A.inclusionHom h) ≫
      (etaleAssociatedReduction X Y (homOfLE (Nat.sub_le m m')).op).app A.diagram = 0 :=
    ((etaleAssociatedFunctor X (Y.action (op m))).map_comp _ _).symm.trans
      ((congrArg (etaleAssociatedFunctor X (Y.action (op m))).map (A.shortComplex h).zero).trans
        (Functor.map_zero _ _ _))
  refine (Category.assoc
    ((etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op).hom.app A.diagram)
    ((etaleAssociatedFunctor X (Y.action (op m))).map (A.inclusionHom h))
    ((etaleAssociatedVaryingSystem X Y hY A.diagram).map
      (homOfLE (Nat.sub_le m m')).op)).trans ((congrArg (_ ≫ ·) ?_).trans comp_zero)
  exact (Category.assoc ((etaleAssociatedFunctor X (Y.action (op m))).map (A.inclusionHom h))
    ((etaleAssociatedReduction X Y (homOfLE (Nat.sub_le m m')).op).app A.diagram)
    ((etaleAssociatedComparisonIso X Y hY (homOfLE (Nat.sub_le m m')).op).inv.app
      A.diagram)).symm.trans ((congrArg (· ≫ (etaleAssociatedComparisonIso X Y hY
        (homOfLE (Nat.sub_le m m')).op).inv.app A.diagram) key).trans zero_comp)

/-- The sequence `0 ⟶ 𝓛 m' ⟶ 𝓛 m ⟶ 𝓛 (m - m') ⟶ 0` of (2.1) is short exact. -/
lemma etale_shortExact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (A.etaleInclusion X Y hY h)
      ((etaleAssociatedVaryingSystem X Y hY A.diagram).map (homOfLE (Nat.sub_le m m')).op)
      (A.etaleInclusion_comp X Y hY h)).ShortExact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := R) X (Y.action (op m)) (hY (op m))
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := R) X (Y.action (op m)) (hY (op m))
  exact ShortComplex.shortExact_of_iso
    (S₁ := (A.shortComplex h).map (etaleAssociatedFunctor X (Y.action (op m))))
    (ShortComplex.isoMk
    ((etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op).app A.diagram).symm (Iso.refl _)
    ((etaleAssociatedComparisonIso X Y hY (homOfLE (Nat.sub_le m m')).op).app A.diagram).symm
    ((Iso.inv_hom_id_app_assoc (etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op)
      A.diagram _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans rfl)) ((A.shortComplex_shortExact h).map_of_exact
      (etaleAssociatedFunctor X (Y.action (op m))))

/-- `i : 𝓛 m' ⟶ 𝓛 m` is a kernel of `ℓ ^ m'` on `𝓛 m`: the sequence is exact. -/
lemma etale_torsion_exact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (A.etaleInclusion X Y hY h)
      (powSMul ℓ m' ((etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op m)))
      (by rw [comp_powSMul, A.etale_powSMul_eq_zero, zero_comp])).Exact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := R) X (Y.action (op m)) (hY (op m))
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := R) X (Y.action (op m)) (hY (op m))
  exact ShortComplex.exact_of_iso
    (S₁ := (A.torsionShortComplex h).map (etaleAssociatedFunctor X (Y.action (op m))))
    (ShortComplex.isoMk
    ((etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op).app A.diagram).symm (Iso.refl _)
    (Iso.refl _)
    ((Iso.inv_hom_id_app_assoc (etaleAssociatedComparisonIso X Y hY (homOfLE h.le).op)
      A.diagram _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans ((map_powSMul (etaleAssociatedFunctor X (Y.action (op m)))
      ℓ m' _).symm.trans (Category.comp_id _).symm)))
    ((A.torsionShortComplex_exact h).map (etaleAssociatedFunctor X (Y.action (op m))))

/-- The sequence `𝓛 (a + b) ⟶ 𝓛 (a + b) ⟶ 𝓛 (a + b)` given by `ℓ ^ a` and `ℓ ^ b` is
exact. -/
lemma etale_flat (a b : ℕ) :
    (ShortComplex.mk
      (powSMul ℓ a ((etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op (a + b))))
      (powSMul ℓ b ((etaleAssociatedVaryingSystem X Y hY A.diagram).obj (op (a + b))))
      (by rw [powSMul_comp_powSMul, A.etale_powSMul_eq_zero])).Exact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := R) X (Y.action (op (a + b)))
    (hY (op (a + b)))
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := R) X (Y.action (op (a + b)))
    (hY (op (a + b)))
  exact shortComplex_exact_congr
    (map_powSMul (etaleAssociatedFunctor X (Y.action (op (a + b)))) ℓ a _)
    (map_powSMul (etaleAssociatedFunctor X (Y.action (op (a + b)))) ℓ b _)
    ((A.flatShortComplex_exact a b).map (etaleAssociatedFunctor X (Y.action (op (a + b)))))

/-- The `ℓ`-divisible system of associated étale sheaves `𝓛 m` on the varying finite étale
torsors `Y m`: its inverse system is the published `etaleAssociatedVaryingSystem`, and its
maps `i` are `etaleInclusion`. -/
@[simps tower]
def etaleSystem : DivisibleSystem (CategoryTheory.Sheaf (Scheme.smallEtaleTopology X)
    (ModuleCat.{u} R)) ℓ where
  tower := etaleAssociatedVaryingSystem X Y hY A.diagram
  inclusion h := A.etaleInclusion X Y hY h
  powSMul_eq_zero m := A.etale_powSMul_eq_zero X Y hY m
  inclusion_comp h := A.etaleInclusion_comp X Y hY h
  shortExact h := A.etale_shortExact X Y hY h
  torsion_exact h := A.etale_torsion_exact X Y hY h
  flat a b := A.etale_flat X Y hY a b

lemma etaleSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (A.etaleSystem X Y hY).inclusion h = A.etaleInclusion X Y hY h :=
  rfl

end EquivariantStructure

end Etale

section Harris

open Langlands.Global Langlands.Shimura Langlands.Shimura.Coefficients

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- The `ℓ`-divisible system of `HarrisCoefficientIntegers L p`-modules `𝓛 / ℓ ^ m 𝓛`, whose
inverse system is the underlying system of the published `harrisCoefficientDiagram ρ p U ℓ`. -/
def harrisTorsionDivisibleSystem :
    DivisibleSystem (ModuleCat.{u} (HarrisCoefficientIntegers L p)) ℓ :=
  ((harrisReductionSystem ℓ ρ p U).ofTowerIso (harrisReductionSystemTowerIso ℓ ρ p U)).map
    (Action.forget _ U.subgroup)

lemma harrisTorsionDivisibleSystem_tower :
    (harrisTorsionDivisibleSystem ℓ ρ p U).tower = (harrisCoefficientDiagram ρ p U ℓ).obj :=
  rfl

/-- The actions of the finite congruence quotients `U / U(ℓ ^ m)` on `𝓛 / ℓ ^ m 𝓛` from the
published `harrisCoefficientDiagram`; the maps `i` are equivariant. -/
def harrisEquivariantStructure :
    (harrisTorsionDivisibleSystem ℓ ρ p U).EquivariantStructure
      (harrisCongruenceGroups ρ p U ℓ) where
  act := (harrisCoefficientDiagram ρ p U ℓ).ρ
  comm := (harrisCoefficientDiagram ρ p U ℓ).comm
  inclusion_comm {m' m} h g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      exact ((harrisReductionSystem ℓ ρ p U).ofTowerIso
        (harrisReductionSystemTowerIso ℓ ρ p U)).inclusion h |>.comm g

lemma harrisEquivariantStructure_diagram :
    (harrisEquivariantStructure ℓ ρ p U).diagram = harrisCoefficientDiagram ρ p U ℓ :=
  rfl

variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

/-- Harris's lisse étale sheaves `𝓛 m` on genuine finite étale torsors form an `ℓ`-divisible
system; its inverse system is the published `harrisEtaleCoefficientSystem`. -/
def harrisEtaleDivisibleSystem :
    DivisibleSystem (CategoryTheory.Sheaf (Scheme.smallEtaleTopology X)
      (ModuleCat.{u} (HarrisCoefficientIntegers L p))) ℓ :=
  (harrisEquivariantStructure ℓ ρ p U).etaleSystem X Y hY

lemma harrisEtaleDivisibleSystem_tower :
    (harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).tower =
      harrisEtaleCoefficientSystem ρ p U ℓ X Y hY :=
  rfl

/-- Global sections of Harris's étale `ℓ`-divisible system, given that the sections of the
maps `j` are surjective. Its inverse system is the published `harrisEtaleSectionsSystem`. -/
def harrisEtaleSectionsDivisibleSystem
    (hΓ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Langlands.Geometry.EtaleDerivedSections.sections X
        (HarrisCoefficientIntegers L p)).map
          ((harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h))) :
    DivisibleSystem (ModuleCat.{u} (HarrisCoefficientIntegers L p)) ℓ :=
  (harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).mapLeftExact
    (Langlands.Geometry.EtaleDerivedSections.sections X (HarrisCoefficientIntegers L p)) hΓ

lemma harrisEtaleSectionsDivisibleSystem_tower
    (hΓ : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Langlands.Geometry.EtaleDerivedSections.sections X
        (HarrisCoefficientIntegers L p)).map
          ((harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).projection h))) :
    (harrisEtaleSectionsDivisibleSystem ℓ ρ p U X Y hY hΓ).tower =
      harrisEtaleSectionsSystem ρ p U ℓ X Y hY :=
  rfl

end Harris

end DivisibleSystem

end Langlands.Cohomology
