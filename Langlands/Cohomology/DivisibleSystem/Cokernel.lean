import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.Refinements
import Langlands.Cohomology.DivisibleSystem

/-!
# Cokernels of `ℓ`-divisible systems

Harris 1999, §2, p.304: if `b : T ⟶ T'` is a morphism of `ℓ`-divisible systems whose
components `b_m` are monomorphisms, then the cokernels `coker b_m` again form an
`ℓ`-divisible system. The rows (2.1) of the cokernel system are exact by the snake lemma;
flatness follows by a diagram chase, and the torsion condition follows from flatness and
the rows.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

namespace DivisibleSystem

/-- Flatness at an index `n = a + b` given by an equation. -/
lemma flat_of_eq (T : DivisibleSystem C ℓ) {a b n : ℕ} (h : a + b = n) :
    (ShortComplex.mk (powSMul ℓ a (T.obj n)) (powSMul ℓ b (T.obj n))
      (by rw [powSMul_comp_powSMul, h, T.powSMul_eq_zero])).Exact := by
  subst h
  exact T.flat a b

/-- The torsion condition of an `ℓ`-divisible system follows from the other conditions:
the kernel of `ℓ ^ m'` on `T m` is the image of `ℓ ^ (m - m')` by flatness, which lies in
the kernel of `j`, that is, in the image of `i`. -/
lemma torsion_exact_of_flat (tower : ℕᵒᵖ ⥤ C)
    (inclusion : ∀ {m' m : ℕ}, m' < m → (tower.obj (op m') ⟶ tower.obj (op m)))
    (powSMul_eq_zero : ∀ m : ℕ, powSMul ℓ m (tower.obj (op m)) = 0)
    (inclusion_comp : ∀ {m' m : ℕ} (h : m' < m),
      inclusion h ≫ tower.map (homOfLE (Nat.sub_le m m')).op = 0)
    (shortExact : ∀ {m' m : ℕ} (h : m' < m),
      (ShortComplex.mk (inclusion h) (tower.map (homOfLE (Nat.sub_le m m')).op)
        (inclusion_comp h)).ShortExact)
    (flat : ∀ a b : ℕ,
      (ShortComplex.mk (powSMul ℓ a (tower.obj (op (a + b))))
        (powSMul ℓ b (tower.obj (op (a + b))))
        (by rw [powSMul_comp_powSMul, powSMul_eq_zero])).Exact)
    {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (inclusion h) (powSMul ℓ m' (tower.obj (op m)))
      (by rw [comp_powSMul, powSMul_eq_zero, zero_comp])).Exact := by
  have flat' : ∀ n : ℕ, (hn : m - m' + m' = n) →
      (ShortComplex.mk (powSMul ℓ (m - m') (tower.obj (op n)))
        (powSMul ℓ m' (tower.obj (op n)))
        (by rw [powSMul_comp_powSMul, hn, powSMul_eq_zero])).Exact := by
    rintro n rfl
    exact flat _ _
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, _, y, hy⟩ :=
    (flat' m (Nat.sub_add_cancel h.le)).exact_up_to_refinements x₂ hx₂
  have hj : (π₁ ≫ x₂) ≫ tower.map (homOfLE (Nat.sub_le m m')).op = 0 := by
    dsimp at hy
    rw [hy, Category.assoc, ← comp_powSMul, powSMul_eq_zero, comp_zero, comp_zero]
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (shortExact h).exact.exact_up_to_refinements _ hj
  exact ⟨A₂, π₂ ≫ π₁, inferInstance, x₁, by simpa only [Category.assoc] using hx₁⟩

/-- Construct an `ℓ`-divisible system without the torsion condition, which follows from
the short exact rows and flatness (`torsion_exact_of_flat`). -/
@[simps tower]
def ofFlat (tower : ℕᵒᵖ ⥤ C)
    (inclusion : ∀ {m' m : ℕ}, m' < m → (tower.obj (op m') ⟶ tower.obj (op m)))
    (powSMul_eq_zero : ∀ m : ℕ, powSMul ℓ m (tower.obj (op m)) = 0)
    (inclusion_comp : ∀ {m' m : ℕ} (h : m' < m),
      inclusion h ≫ tower.map (homOfLE (Nat.sub_le m m')).op = 0)
    (shortExact : ∀ {m' m : ℕ} (h : m' < m),
      (ShortComplex.mk (inclusion h) (tower.map (homOfLE (Nat.sub_le m m')).op)
        (inclusion_comp h)).ShortExact)
    (flat : ∀ a b : ℕ,
      (ShortComplex.mk (powSMul ℓ a (tower.obj (op (a + b))))
        (powSMul ℓ b (tower.obj (op (a + b))))
        (by rw [powSMul_comp_powSMul, powSMul_eq_zero])).Exact) :
    DivisibleSystem C ℓ where
  tower := tower
  inclusion := inclusion
  powSMul_eq_zero := powSMul_eq_zero
  inclusion_comp := inclusion_comp
  shortExact := shortExact
  torsion_exact h :=
    torsion_exact_of_flat tower inclusion powSMul_eq_zero inclusion_comp shortExact flat h
  flat := flat

@[simp]
lemma ofFlat_inclusion (tower : ℕᵒᵖ ⥤ C)
    (inclusion : ∀ {m' m : ℕ}, m' < m → (tower.obj (op m') ⟶ tower.obj (op m)))
    (powSMul_eq_zero : ∀ m : ℕ, powSMul ℓ m (tower.obj (op m)) = 0)
    (inclusion_comp : ∀ {m' m : ℕ} (h : m' < m),
      inclusion h ≫ tower.map (homOfLE (Nat.sub_le m m')).op = 0)
    (shortExact : ∀ {m' m : ℕ} (h : m' < m),
      (ShortComplex.mk (inclusion h) (tower.map (homOfLE (Nat.sub_le m m')).op)
        (inclusion_comp h)).ShortExact)
    (flat : ∀ a b : ℕ,
      (ShortComplex.mk (powSMul ℓ a (tower.obj (op (a + b))))
        (powSMul ℓ b (tower.obj (op (a + b))))
        (by rw [powSMul_comp_powSMul, powSMul_eq_zero])).Exact)
    {m' m : ℕ} (h : m' < m) :
    (ofFlat tower inclusion powSMul_eq_zero inclusion_comp shortExact flat).inclusion h =
      inclusion h :=
  rfl

section Cokernel

open ZeroObject

variable {T T' : DivisibleSystem C ℓ} (b : T ⟶ T')

/-- The objects `coker b_m` with the maps induced by the maps `j`. -/
def cokernelTower : ℕᵒᵖ ⥤ C where
  obj m := cokernel (b.tower.app m)
  map {m n} f := cokernel.map (b.tower.app m) (b.tower.app n) (T.tower.map f)
    (T'.tower.map f) (b.tower.naturality f).symm
  map_id m := by
    ext
    simp
  map_comp f g := by
    ext
    simp

/-- The projection `T' m ⟶ coker b_m`. -/
def cokernelπ (m : ℕᵒᵖ) : T'.tower.obj m ⟶ (cokernelTower b).obj m :=
  cokernel.π (b.tower.app m)

instance (m : ℕᵒᵖ) : Epi (cokernelπ b m) :=
  show Epi (cokernel.π (b.tower.app m)) from inferInstance

@[reassoc (attr := simp)]
lemma comp_cokernelπ (m : ℕᵒᵖ) : b.tower.app m ≫ cokernelπ b m = 0 :=
  cokernel.condition _

/-- `cokernelπ b m` is a cokernel of `b_m`. -/
def cokernelπIsCokernel (m : ℕᵒᵖ) :
    IsColimit (CokernelCofork.ofπ (cokernelπ b m) (comp_cokernelπ b m)) :=
  cokernelIsCokernel _

/-- The map out of `coker b_m` induced by a map out of `T' m` vanishing on the image
of `b_m`. -/
def cokernelDesc {m : ℕᵒᵖ} {X : C} (g : T'.tower.obj m ⟶ X)
    (hg : b.tower.app m ≫ g = 0) : (cokernelTower b).obj m ⟶ X :=
  cokernel.desc _ g hg

@[reassoc (attr := simp)]
lemma cokernelπ_desc {m : ℕᵒᵖ} {X : C} (g : T'.tower.obj m ⟶ X)
    (hg : b.tower.app m ≫ g = 0) : cokernelπ b m ≫ cokernelDesc b g hg = g :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma cokernelπ_map {m n : ℕᵒᵖ} (f : m ⟶ n) :
    cokernelπ b m ≫ (cokernelTower b).map f = T'.tower.map f ≫ cokernelπ b n := by
  simp [cokernelTower, cokernelπ]

/-- The map `coker b_{m'} ⟶ coker b_m` induced by the maps `i`. -/
def cokernelInclusion {m' m : ℕ} (h : m' < m) :
    (cokernelTower b).obj (op m') ⟶ (cokernelTower b).obj (op m) :=
  cokernel.map _ _ (T.inclusion h) (T'.inclusion h) (b.comm h).symm

@[reassoc (attr := simp)]
lemma cokernelπ_inclusion {m' m : ℕ} (h : m' < m) :
    cokernelπ b (op m') ≫ cokernelInclusion b h = T'.inclusion h ≫ cokernelπ b (op m) :=
  cokernel.π_desc _ _ _

lemma cokernel_powSMul_eq_zero (m : ℕ) :
    powSMul ℓ m ((cokernelTower b).obj (op m)) = 0 := by
  rw [← cancel_epi (cokernelπ b (op m)), comp_powSMul, T'.powSMul_eq_zero, zero_comp,
    comp_zero]

lemma cokernelInclusion_comp {m' m : ℕ} (h : m' < m) :
    cokernelInclusion b h ≫ (cokernelTower b).map (homOfLE (Nat.sub_le m m')).op = 0 := by
  rw [← cancel_epi (cokernelπ b (op m')), comp_zero, cokernelπ_inclusion_assoc,
    cokernelπ_map, reassoc_of% T'.inclusion_comp h, zero_comp]

variable [hb : ∀ m : ℕ, Mono (b.tower.app (op m))]

/-- The snake diagram whose rows are the sequences (2.1) of `T`, `T'` and the cokernels,
with a zero row of kernels. -/
def cokernelSnakeInput {m' m : ℕ} (h : m' < m) : ShortComplex.SnakeInput C where
  L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) comp_zero
  L₁ := ShortComplex.mk _ _ (T.inclusion_comp h)
  L₂ := ShortComplex.mk _ _ (T'.inclusion_comp h)
  L₃ := ShortComplex.mk _ _ (cokernelInclusion_comp b h)
  v₀₁ := { τ₁ := 0, τ₂ := 0, τ₃ := 0 }
  v₁₂ :=
    { τ₁ := b.tower.app (op m')
      τ₂ := b.tower.app (op m)
      τ₃ := b.tower.app (op (m - m'))
      comm₁₂ := (b.comm h).symm
      comm₂₃ := (b.tower.naturality _).symm }
  v₂₃ :=
    { τ₁ := cokernelπ b _
      τ₂ := cokernelπ b _
      τ₃ := cokernelπ b _
      comm₁₂ := cokernelπ_inclusion b h
      comm₂₃ := cokernelπ_map b _ }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ (hb _) (isZero_zero C))
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm (cokernelπIsCokernel b _)
  L₁_exact := (T.shortExact h).exact
  epi_L₁_g := (T.shortExact h).epi_g
  L₂_exact := (T'.shortExact h).exact
  mono_L₂_f := (T'.shortExact h).mono_f

lemma cokernel_shortExact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (cokernelInclusion b h)
      ((cokernelTower b).map (homOfLE (Nat.sub_le m m')).op)
      (cokernelInclusion_comp b h)).ShortExact := by
  let S := cokernelSnakeInput b h
  have : Epi S.L₂.g := (T'.shortExact h).epi_g
  have hδ : S.L₂'.f = 0 := (isZero_zero C).eq_of_src _ _
  exact { exact := S.L₃_exact, mono_f := S.L₂'_exact.mono_g hδ, epi_g := S.epi_L₃_g }

lemma cokernel_flat (a c : ℕ) :
    (ShortComplex.mk (powSMul ℓ a ((cokernelTower b).obj (op (a + c))))
      (powSMul ℓ c ((cokernelTower b).obj (op (a + c))))
      (by rw [powSMul_comp_powSMul, cokernel_powSMul_eq_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  rintro A (z : A ⟶ (cokernelTower b).obj (op (a + c)))
    (hz : z ≫ powSMul ℓ c ((cokernelTower b).obj (op (a + c))) = 0)
  obtain ⟨A₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (cokernelπ b (op (a + c))) z
  have h₁ : (y ≫ powSMul ℓ c (T'.obj (a + c))) ≫ cokernelπ b (op (a + c)) = 0 := by
    rw [Category.assoc, ← comp_powSMul, ← reassoc_of% hy, hz, comp_zero]
  have ex : (ShortComplex.mk (b.tower.app (op (a + c))) (cokernelπ b (op (a + c)))
      (comp_cokernelπ b _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelπIsCokernel b _)
  obtain ⟨A₂, π₂, _, (x : A₂ ⟶ T.obj (a + c)),
    (hx : π₂ ≫ y ≫ powSMul ℓ c (T'.obj (a + c)) = x ≫ b.tower.app (op (a + c)))⟩ :=
    ex.exact_up_to_refinements _ h₁
  have h₂ : x ≫ powSMul ℓ a (T.obj (a + c)) = 0 := by
    rw [← cancel_mono (b.tower.app (op (a + c))), zero_comp, Category.assoc, ← comp_powSMul,
      ← reassoc_of% hx, powSMul_comp_powSMul, add_comm c a, T'.powSMul_eq_zero, comp_zero,
      comp_zero]
  obtain ⟨A₃, π₃, _, (x₀ : A₃ ⟶ T.obj (a + c)),
    (hx₀ : π₃ ≫ x = x₀ ≫ powSMul ℓ c (T.obj (a + c)))⟩ :=
    (T.flat_of_eq (add_comm c a)).exact_up_to_refinements x h₂
  have h₃ : (π₃ ≫ π₂ ≫ y - x₀ ≫ b.tower.app (op (a + c))) ≫
      powSMul ℓ c (T'.obj (a + c)) = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero]
    simp only [Category.assoc]
    rw [hx, reassoc_of% hx₀, comp_powSMul]
  obtain ⟨A₄, π₄, _, (w : A₄ ⟶ T'.obj (a + c)),
    (hw : π₄ ≫ (π₃ ≫ π₂ ≫ y - x₀ ≫ b.tower.app (op (a + c))) =
      w ≫ powSMul ℓ a (T'.obj (a + c)))⟩ :=
    (T'.flat a c).exact_up_to_refinements _ h₃
  refine ⟨A₄, π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance, w ≫ cokernelπ b _, ?_⟩
  show (π₄ ≫ π₃ ≫ π₂ ≫ π₁) ≫ z =
    (w ≫ cokernelπ b _) ≫ powSMul ℓ a ((cokernelTower b).obj (op (a + c)))
  simp only [Category.assoc]
  rw [comp_powSMul, ← reassoc_of% hw, Preadditive.sub_comp]
  simp only [Category.assoc, comp_cokernelπ, comp_zero, sub_zero, hy]

/-- The cokernel `ℓ`-divisible system `{coker b_m}` of a morphism `b` of `ℓ`-divisible
systems whose components are monomorphisms (Harris 1999, p.304). -/
def cokernelSystem : DivisibleSystem C ℓ :=
  ofFlat (cokernelTower b) (cokernelInclusion b) (cokernel_powSMul_eq_zero b)
    (cokernelInclusion_comp b) (cokernel_shortExact b) (cokernel_flat b)

@[simp]
lemma cokernelSystem_tower : (cokernelSystem b).tower = cokernelTower b :=
  rfl

lemma cokernelSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (cokernelSystem b).inclusion h = cokernelInclusion b h :=
  rfl

/-- The projection `T' ⟶ {coker b_m}`. -/
def toCokernelSystem : T' ⟶ cokernelSystem b where
  tower :=
    { app := fun m => cokernelπ b m
      naturality := fun _ _ f => (cokernelπ_map b f).symm }
  comm h := (cokernelπ_inclusion b h).symm

lemma toCokernelSystem_tower_app (m : ℕᵒᵖ) :
    (toCokernelSystem b).tower.app m = cokernelπ b m :=
  rfl

instance (m : ℕᵒᵖ) : Epi ((toCokernelSystem b).tower.app m) :=
  show Epi (cokernelπ b m) from inferInstance

@[reassoc (attr := simp)]
lemma comp_toCokernelSystem_tower_app (m : ℕᵒᵖ) :
    b.tower.app m ≫ (toCokernelSystem b).tower.app m = 0 :=
  comp_cokernelπ b m

/-- Each level `0 ⟶ T m ⟶ T' m ⟶ coker b_m ⟶ 0` is short exact. -/
lemma shortExact_app (m : ℕ) :
    (ShortComplex.mk (b.tower.app (op m)) ((toCokernelSystem b).tower.app (op m))
      (comp_toCokernelSystem_tower_app b _)).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelπIsCokernel b _)
    mono_f := hb m
    epi_g := (inferInstance : Epi ((toCokernelSystem b).tower.app (op m))) }

/-- A morphism `g : T' ⟶ T''` with `b_m ≫ g_m = 0` for all `m` factors through the cokernel
system. -/
def cokernelSystemDesc {T'' : DivisibleSystem C ℓ} (g : T' ⟶ T'')
    (hg : ∀ m : ℕᵒᵖ, b.tower.app m ≫ g.tower.app m = 0) : cokernelSystem b ⟶ T'' where
  tower :=
    { app := fun m => cokernelDesc b (g.tower.app m) (hg m)
      naturality := fun m n f => by
        show (cokernelTower b).map f ≫ cokernelDesc b _ (hg n) =
          cokernelDesc b _ (hg m) ≫ T''.tower.map f
        rw [← cancel_epi (cokernelπ b m), cokernelπ_map_assoc, cokernelπ_desc,
          cokernelπ_desc_assoc, g.tower.naturality] }
  comm {m' m} h := by
    show cokernelInclusion b h ≫ cokernelDesc b _ (hg (op m)) =
      cokernelDesc b _ (hg (op m')) ≫ T''.inclusion h
    rw [← cancel_epi (cokernelπ b (op m')), cokernelπ_inclusion_assoc, cokernelπ_desc,
      cokernelπ_desc_assoc, g.comm h]

@[reassoc (attr := simp)]
lemma toCokernelSystem_desc {T'' : DivisibleSystem C ℓ} (g : T' ⟶ T'')
    (hg : ∀ m : ℕᵒᵖ, b.tower.app m ≫ g.tower.app m = 0) :
    toCokernelSystem b ≫ cokernelSystemDesc b g hg = g := by
  ext m
  exact cokernelπ_desc b _ _

lemma cokernelSystem_hom_ext {T'' : DivisibleSystem C ℓ} {f g : cokernelSystem b ⟶ T''}
    (h : toCokernelSystem b ≫ f = toCokernelSystem b ≫ g) : f = g := by
  ext m
  rw [← cancel_epi ((toCokernelSystem b).tower.app m)]
  exact congrArg (fun φ => φ.tower.app m) h

end Cokernel

end DivisibleSystem

end Langlands.Cohomology
