import Langlands.Cohomology.DivisibleSystem.Cokernel
import Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective

/-!
# The `ℓ`-divisible system of reductions of an `ℓ`-torsion-free object

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, p.311: for an
`𝒪`-lattice `𝓛` in a representation of `K_ℓ`, "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m`
forms an inverse system of `𝒪`-modules". Here `𝓛 ⊗_𝒪 𝒪_m = 𝓛 / ℓ^m 𝓛`.

For an object `L` of an abelian category on which multiplication by `ℓ` is a monomorphism, the
cokernels `L / ℓ ^ m L` of multiplication by `ℓ ^ m` form an `ℓ`-divisible system in the sense
of Harris's (2.1): the map `i : L / ℓ ^ m' L ⟶ L / ℓ ^ m L` is induced by `ℓ ^ (m - m')`, the
map `j : L / ℓ ^ m L ⟶ L / ℓ ^ (m - m') L` is the projection, the rows are short exact by the
snake lemma, and flatness follows by a diagram chase. The construction is functorial in `L`
(`reductionFunctor`). In a category of representations the hypothesis says that `ℓ` is a
non-zero-divisor on the underlying module (`mono_powSMul_one_iff_isSMulRegular`).
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u' v'

section Mono

variable {C : Type u} [Category.{v} C] [Preadditive C] (ℓ : ℕ)

/-- If multiplication by `ℓ` on `L` is a monomorphism, so is multiplication by `ℓ ^ m`. -/
lemma mono_powSMul (L : C) [Mono (powSMul ℓ 1 L)] (m : ℕ) : Mono (powSMul ℓ m L) := by
  induction m with
  | zero =>
    rw [powSMul_zero]
    infer_instance
  | succ m ih =>
    rw [← powSMul_comp_powSMul ℓ m 1]
    exact mono_comp _ _

/-- In a category of representations, multiplication by `ℓ` is a monomorphism exactly when the
scalar `ℓ` is a non-zero-divisor on the underlying module. -/
lemma mono_powSMul_one_iff_isSMulRegular {R : Type u} [CommRing R] {G : Type v} [Monoid G]
    (X : Rep.{w} R G) : Mono (powSMul ℓ 1 X) ↔ IsSMulRegular X (ℓ : R) := by
  rw [Rep.mono_iff_injective]
  have h : ⇑(powSMul ℓ 1 X).hom = fun x : X => (ℓ : R) • x :=
    funext fun x => by rw [powSMul_hom_apply, pow_one]
  rw [h]
  rfl

end Mono

namespace DivisibleSystem

variable {C : Type u} [Category.{v} C] [Abelian C] (ℓ : ℕ)

section Reduction

open ZeroObject

variable (L : C)

/-- For `n ≤ m`, multiplication by `ℓ ^ m` followed by the projection onto `L / ℓ ^ n L` is
zero. -/
lemma powSMul_comp_cokernelπ_of_le {n m : ℕ} (h : n ≤ m) :
    powSMul ℓ m L ≫ cokernel.π (powSMul ℓ n L) = 0 := by
  rw [← Nat.sub_add_cancel h, ← powSMul_comp_powSMul, Category.assoc, cokernel.condition,
    comp_zero]

/-- The objects `L / ℓ ^ m L`, cokernels of multiplication by `ℓ ^ m`, with the projections
`L / ℓ ^ m L ⟶ L / ℓ ^ n L` for `n ≤ m`. -/
def reductionTower : ℕᵒᵖ ⥤ C where
  obj m := cokernel (powSMul ℓ m.unop L)
  map {m n} f := cokernel.desc _ (cokernel.π (powSMul ℓ n.unop L))
    (powSMul_comp_cokernelπ_of_le ℓ L (leOfHom f.unop))
  map_id m := by
    ext
    simp
  map_comp f g := by
    ext
    simp

/-- The projection `L ⟶ L / ℓ ^ m L`. -/
def reductionπ (m : ℕ) : L ⟶ (reductionTower ℓ L).obj (op m) :=
  cokernel.π (powSMul ℓ m L)

instance (m : ℕ) : Epi (reductionπ ℓ L m) :=
  show Epi (cokernel.π _) from inferInstance

/-- Multiplication by `ℓ ^ m` followed by the projection onto `L / ℓ ^ m L` is zero. -/
@[reassoc (attr := simp)]
lemma powSMul_comp_reductionπ (m : ℕ) : powSMul ℓ m L ≫ reductionπ ℓ L m = 0 :=
  cokernel.condition _

/-- For `n ≤ m`, multiplication by `ℓ ^ m` followed by the projection onto `L / ℓ ^ n L` is
zero. -/
lemma powSMul_comp_reductionπ_of_le {n m : ℕ} (h : n ≤ m) :
    powSMul ℓ m L ≫ reductionπ ℓ L n = 0 :=
  powSMul_comp_cokernelπ_of_le ℓ L h

/-- `reductionπ ℓ L m` is a cokernel of multiplication by `ℓ ^ m`. -/
def reductionπIsCokernel (m : ℕ) :
    IsColimit (CokernelCofork.ofπ (reductionπ ℓ L m) (powSMul_comp_reductionπ ℓ L m)) :=
  cokernelIsCokernel _

/-- The transition maps of `reductionTower ℓ L` commute with the projections from `L`. -/
@[reassoc (attr := simp)]
lemma reductionπ_map {m n : ℕ} (f : (op m : ℕᵒᵖ) ⟶ op n) :
    reductionπ ℓ L m ≫ (reductionTower ℓ L).map f = reductionπ ℓ L n :=
  cokernel.π_desc _ _ _

/-- The map `i : L / ℓ ^ m' L ⟶ L / ℓ ^ m L` induced by multiplication by `ℓ ^ (m - m')`. -/
def reductionInclusion {m' m : ℕ} (h : m' < m) :
    (reductionTower ℓ L).obj (op m') ⟶ (reductionTower ℓ L).obj (op m) :=
  cokernel.desc _ (powSMul ℓ (m - m') L ≫ reductionπ ℓ L m) (by
    rw [← Category.assoc, powSMul_comp_powSMul, Nat.add_sub_of_le h.le,
      powSMul_comp_reductionπ])

/-- The map `i` sends the class of `x` to the class of `ℓ ^ (m - m') x`. -/
@[reassoc (attr := simp)]
lemma reductionπ_inclusion {m' m : ℕ} (h : m' < m) :
    reductionπ ℓ L m' ≫ reductionInclusion ℓ L h = powSMul ℓ (m - m') L ≫ reductionπ ℓ L m :=
  cokernel.π_desc _ _ _

/-- Multiplication by `ℓ ^ m` is zero on `L / ℓ ^ m L`. -/
lemma reduction_powSMul_eq_zero (m : ℕ) :
    powSMul ℓ m ((reductionTower ℓ L).obj (op m)) = 0 := by
  rw [← cancel_epi (reductionπ ℓ L m), comp_powSMul, powSMul_comp_reductionπ, comp_zero]

/-- The map `i : L / ℓ ^ m' L ⟶ L / ℓ ^ m L` followed by the projection onto
`L / ℓ ^ (m - m') L` is zero. -/
lemma reductionInclusion_comp {m' m : ℕ} (h : m' < m) :
    reductionInclusion ℓ L h ≫ (reductionTower ℓ L).map (homOfLE (Nat.sub_le m m')).op = 0 := by
  rw [← cancel_epi (reductionπ ℓ L m'), comp_zero, reductionπ_inclusion_assoc, reductionπ_map,
    powSMul_comp_reductionπ]

/-- Each level `0 ⟶ L ⟶ L ⟶ L / ℓ ^ m L ⟶ 0`, with first map `ℓ ^ m`, is short exact. -/
lemma shortExact_powSMul_reductionπ [Mono (powSMul ℓ 1 L)] (m : ℕ) :
    (ShortComplex.mk (powSMul ℓ m L) (reductionπ ℓ L m)
      (powSMul_comp_reductionπ ℓ L m)).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (reductionπIsCokernel ℓ L m)
    mono_f := mono_powSMul ℓ L m
    epi_g := (inferInstance : Epi (reductionπ ℓ L m)) }

variable [Mono (powSMul ℓ 1 L)]

/-- The snake diagram with rows `L = L ⟶ 0`, `L ⟶ L ⟶ L / ℓ ^ (m - m') L` (multiplication by
`ℓ ^ (m - m')`, then the projection) and the sequence (2.1) of the reductions, with vertical maps
`ℓ ^ m'`, `ℓ ^ m`, `0` and a zero row of kernels. -/
def reductionSnakeInput {m' m : ℕ} (h : m' < m) : ShortComplex.SnakeInput C where
  L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) comp_zero
  L₁ := ShortComplex.mk (𝟙 L) (0 : L ⟶ 0) comp_zero
  L₂ := ShortComplex.mk _ _ (powSMul_comp_reductionπ ℓ L (m - m'))
  L₃ := ShortComplex.mk _ _ (reductionInclusion_comp ℓ L h)
  v₀₁ := { τ₁ := 0, τ₂ := 0, τ₃ := 0 }
  v₁₂ :=
    { τ₁ := powSMul ℓ m' L
      τ₂ := powSMul ℓ m L
      τ₃ := 0
      comm₁₂ := by
        dsimp
        rw [Category.id_comp, powSMul_comp_powSMul, Nat.add_sub_of_le h.le]
      comm₂₃ := (powSMul_comp_reductionπ_of_le ℓ L (Nat.sub_le m m')).trans comp_zero.symm }
  v₂₃ :=
    { τ₁ := reductionπ ℓ L m'
      τ₂ := reductionπ ℓ L m
      τ₃ := 𝟙 _
      comm₁₂ := reductionπ_inclusion ℓ L h
      comm₂₃ := (reductionπ_map ℓ L (homOfLE (Nat.sub_le m m')).op).trans
        (Category.comp_id _).symm }
  w₀₂ := by ext
  w₁₃ := by ext <;> simp
  h₀ := by
    have h₀ : Mono (0 : (0 : C) ⟶ (reductionTower ℓ L).obj (op (m - m'))) :=
      ⟨fun g h _ => (isZero_zero C).eq_of_tgt g h⟩
    apply ShortComplex.isLimitOfIsLimitπ
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ (mono_powSMul ℓ L m') (isZero_zero C))
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ (mono_powSMul ℓ L m) (isZero_zero C))
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ h₀ (isZero_zero C))
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm (reductionπIsCokernel ℓ L m')
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm (reductionπIsCokernel ℓ L m)
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (CokernelCofork.IsColimit.ofId _ rfl)
  L₁_exact := (ShortComplex.exact_iff_epi _ rfl).2 (inferInstance : Epi (𝟙 L))
  epi_L₁_g := ⟨fun g h _ => (isZero_zero C).eq_of_src g h⟩
  L₂_exact := ShortComplex.exact_of_g_is_cokernel _ (reductionπIsCokernel ℓ L (m - m'))
  mono_L₂_f := mono_powSMul ℓ L (m - m')

/-- The sequence `0 ⟶ L / ℓ ^ m' L ⟶ L / ℓ ^ m L ⟶ L / ℓ ^ (m - m') L ⟶ 0` of maps `i` and `j`
is short exact (Harris's (2.1)). -/
lemma reduction_shortExact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (reductionInclusion ℓ L h)
      ((reductionTower ℓ L).map (homOfLE (Nat.sub_le m m')).op)
      (reductionInclusion_comp ℓ L h)).ShortExact := by
  let S := reductionSnakeInput ℓ L h
  have : Epi S.L₂.g := (inferInstance : Epi (reductionπ ℓ L (m - m')))
  have hδ : S.L₂'.f = 0 := (isZero_zero C).eq_of_src _ _
  exact { exact := S.L₃_exact, mono_f := S.L₂'_exact.mono_g hδ, epi_g := S.epi_L₃_g }

/-- On `L / ℓ ^ (a + b) L`, the kernel of multiplication by `ℓ ^ b` is the image of
multiplication by `ℓ ^ a`. -/
lemma reduction_flat (a b : ℕ) :
    (ShortComplex.mk (powSMul ℓ a ((reductionTower ℓ L).obj (op (a + b))))
      (powSMul ℓ b ((reductionTower ℓ L).obj (op (a + b))))
      (by rw [powSMul_comp_powSMul, reduction_powSMul_eq_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  rintro A (z : A ⟶ (reductionTower ℓ L).obj (op (a + b)))
    (hz : z ≫ powSMul ℓ b ((reductionTower ℓ L).obj (op (a + b))) = 0)
  obtain ⟨A₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (reductionπ ℓ L (a + b)) z
  have h₁ : (y ≫ powSMul ℓ b L) ≫ reductionπ ℓ L (a + b) = 0 := by
    rw [Category.assoc, ← comp_powSMul, ← reassoc_of% hy, hz, comp_zero]
  obtain ⟨A₂, π₂, _, (x : A₂ ⟶ L), (hx : π₂ ≫ y ≫ powSMul ℓ b L = x ≫ powSMul ℓ (a + b) L)⟩ :=
    (shortExact_powSMul_reductionπ ℓ L (a + b)).exact.exact_up_to_refinements _ h₁
  have h₂ : π₂ ≫ y = x ≫ powSMul ℓ a L := by
    have := mono_powSMul ℓ L b
    rw [← cancel_mono (powSMul ℓ b L), Category.assoc, Category.assoc, powSMul_comp_powSMul, hx]
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, x ≫ reductionπ ℓ L (a + b), ?_⟩
  show (π₂ ≫ π₁) ≫ z =
    (x ≫ reductionπ ℓ L (a + b)) ≫ powSMul ℓ a ((reductionTower ℓ L).obj (op (a + b)))
  rw [Category.assoc, hy, ← Category.assoc, h₂, Category.assoc, Category.assoc, comp_powSMul]

/-- The `ℓ`-divisible system `{L / ℓ ^ m L}` of reductions of an object `L` on which
multiplication by `ℓ` is a monomorphism (Harris 1999, p.311, the system `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m`). -/
def reductionSystem : DivisibleSystem C ℓ :=
  ofFlat (reductionTower ℓ L) (reductionInclusion ℓ L) (reduction_powSMul_eq_zero ℓ L)
    (reductionInclusion_comp ℓ L) (reduction_shortExact ℓ L) (reduction_flat ℓ L)

/-- The tower of `reductionSystem ℓ L` is `reductionTower ℓ L`. -/
@[simp]
lemma reductionSystem_tower : (reductionSystem ℓ L).tower = reductionTower ℓ L :=
  rfl

/-- The maps `i` of `reductionSystem ℓ L` are the maps `reductionInclusion ℓ L`. -/
lemma reductionSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (reductionSystem ℓ L).inclusion h = reductionInclusion ℓ L h :=
  rfl

end Reduction

section Map

variable {L L' L'' : C}

/-- The map `L / ℓ ^ m L ⟶ L' / ℓ ^ m L'` induced by a morphism `f : L ⟶ L'`. -/
def reductionMap (f : L ⟶ L') (m : ℕ) :
    (reductionTower ℓ L).obj (op m) ⟶ (reductionTower ℓ L').obj (op m) :=
  cokernel.desc _ (f ≫ reductionπ ℓ L' m) (by
    rw [← Category.assoc, ← comp_powSMul, Category.assoc, powSMul_comp_reductionπ, comp_zero])

/-- The map induced by `f` sends the class of `x` to the class of `f x`. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionMap (f : L ⟶ L') (m : ℕ) :
    reductionπ ℓ L m ≫ reductionMap ℓ f m = f ≫ reductionπ ℓ L' m :=
  cokernel.π_desc _ _ _

/-- The maps `L / ℓ ^ m L ⟶ L' / ℓ ^ m L'` induced by a morphism `f : L ⟶ L'`, as a morphism
of inverse systems. -/
@[simps]
def reductionTowerMap (f : L ⟶ L') : reductionTower ℓ L ⟶ reductionTower ℓ L' where
  app m := reductionMap ℓ f m.unop
  naturality m n g := by
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    rw [← cancel_epi (reductionπ ℓ L m), reductionπ_map_assoc, reductionπ_reductionMap,
      reductionπ_reductionMap_assoc, reductionπ_map]

/-- The components of `reductionTowerMap ℓ f` commute with the projections. -/
lemma reductionπ_reductionTowerMap_app (f : L ⟶ L') (m : ℕ) :
    reductionπ ℓ L m ≫ (reductionTowerMap ℓ f).app (op m) = f ≫ reductionπ ℓ L' m :=
  reductionπ_reductionMap ℓ f m

/-- The identity of `L` induces the identity of `reductionTower ℓ L`. -/
lemma reductionTowerMap_id : reductionTowerMap ℓ (𝟙 L) = 𝟙 _ := by
  ext m
  induction m using Opposite.rec with | op m =>
  rw [← cancel_epi (reductionπ ℓ L m), reductionTowerMap_app, reductionπ_reductionMap,
    Category.id_comp, NatTrans.id_app, Category.comp_id]

/-- `reductionTowerMap` is compatible with composition. -/
lemma reductionTowerMap_comp (f : L ⟶ L') (g : L' ⟶ L'') :
    reductionTowerMap ℓ (f ≫ g) = reductionTowerMap ℓ f ≫ reductionTowerMap ℓ g := by
  ext m
  induction m using Opposite.rec with | op m =>
  rw [← cancel_epi (reductionπ ℓ L m), NatTrans.comp_app, reductionTowerMap_app,
    reductionTowerMap_app, reductionTowerMap_app, reductionπ_reductionMap,
    reductionπ_reductionMap_assoc, reductionπ_reductionMap, Category.assoc]

variable [Mono (powSMul ℓ 1 L)] [Mono (powSMul ℓ 1 L')] [Mono (powSMul ℓ 1 L'')]

/-- The morphism of `ℓ`-divisible systems `{L / ℓ ^ m L} ⟶ {L' / ℓ ^ m L'}` induced by a
morphism `f : L ⟶ L'`. -/
def reductionSystemMap (f : L ⟶ L') : reductionSystem ℓ L ⟶ reductionSystem ℓ L' where
  tower := reductionTowerMap ℓ f
  comm {m' m} h := by
    change reductionInclusion ℓ L h ≫ reductionMap ℓ f m =
      reductionMap ℓ f m' ≫ reductionInclusion ℓ L' h
    rw [← cancel_epi (reductionπ ℓ L m'), reductionπ_inclusion_assoc,
      reductionπ_reductionMap, reductionπ_reductionMap_assoc,
      reductionπ_inclusion, ← Category.assoc, ← comp_powSMul, Category.assoc]

/-- The underlying morphism of towers of `reductionSystemMap ℓ f` is `reductionTowerMap ℓ f`. -/
@[simp]
lemma reductionSystemMap_tower (f : L ⟶ L') :
    (reductionSystemMap ℓ f).tower = reductionTowerMap ℓ f :=
  rfl

/-- The identity of `L` induces the identity of `reductionSystem ℓ L`. -/
lemma reductionSystemMap_id : reductionSystemMap ℓ (𝟙 L) = 𝟙 (reductionSystem ℓ L) :=
  hom_ext (reductionTowerMap_id ℓ)

/-- `reductionSystemMap` is compatible with composition. -/
lemma reductionSystemMap_comp (f : L ⟶ L') (g : L' ⟶ L'') :
    reductionSystemMap ℓ (f ≫ g) = reductionSystemMap ℓ f ≫ reductionSystemMap ℓ g :=
  hom_ext (reductionTowerMap_comp ℓ f g)

end Map

section Functor

variable (C) in
/-- The objects on which multiplication by `ℓ` is a monomorphism. -/
def powSMulMono : ObjectProperty C := fun L => Mono (powSMul ℓ 1 L)

/-- The reduction `L ↦ {L / ℓ ^ m L}` as a functor on objects on which multiplication by `ℓ` is
a monomorphism. -/
@[simps obj]
def reductionFunctor : (powSMulMono C ℓ).FullSubcategory ⥤ DivisibleSystem C ℓ where
  obj L := @reductionSystem C _ _ ℓ L.obj L.property
  map {L L'} f := @reductionSystemMap C _ _ ℓ L.obj L'.obj L.property L'.property f.hom
  map_id L := @reductionSystemMap_id C _ _ ℓ L.obj L.property
  map_comp {L L' L''} f g :=
    @reductionSystemMap_comp C _ _ ℓ L.obj L'.obj L''.obj L.property L'.property L''.property
      f.hom g.hom

end Functor

end DivisibleSystem

end Langlands.Cohomology
